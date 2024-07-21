//===-- SanitizerCoverage.cpp - coverage instrumentation for sanitizers ---===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Coverage instrumentation done on LLVM IR level, works with Sanitizers.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Instrumentation/SanitizerCoverage.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/Triple.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/EHPersonalities.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Mangler.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/InitializePasses.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/SpecialCaseList.h"
#include "llvm/Support/VirtualFileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include "afl-llvm-common.h"

#include <fstream>
#include <iostream>
#include <chrono>
#include <thread> 
#include <ctime>
#include <cstdlib>
#include <sys/file.h>
#include <fcntl.h>
#include <unistd.h>

using namespace llvm;

#define DEBUG_TYPE "sancov"

const char SanCovTracePCIndirName[] = "__sanitizer_cov_trace_pc_indir";
const char SanCovTracePCName[] = "__sanitizer_cov_trace_pc";
const char SanCovTraceCmp1[] = "__sanitizer_cov_trace_cmp1";
const char SanCovTraceCmp2[] = "__sanitizer_cov_trace_cmp2";
const char SanCovTraceCmp4[] = "__sanitizer_cov_trace_cmp4";
const char SanCovTraceCmp8[] = "__sanitizer_cov_trace_cmp8";
const char SanCovTraceConstCmp1[] = "__sanitizer_cov_trace_const_cmp1";
const char SanCovTraceConstCmp2[] = "__sanitizer_cov_trace_const_cmp2";
const char SanCovTraceConstCmp4[] = "__sanitizer_cov_trace_const_cmp4";
const char SanCovTraceConstCmp8[] = "__sanitizer_cov_trace_const_cmp8";
const char SanCovLoad1[] = "__sanitizer_cov_load1";
const char SanCovLoad2[] = "__sanitizer_cov_load2";
const char SanCovLoad4[] = "__sanitizer_cov_load4";
const char SanCovLoad8[] = "__sanitizer_cov_load8";
const char SanCovLoad16[] = "__sanitizer_cov_load16";
const char SanCovStore1[] = "__sanitizer_cov_store1";
const char SanCovStore2[] = "__sanitizer_cov_store2";
const char SanCovStore4[] = "__sanitizer_cov_store4";
const char SanCovStore8[] = "__sanitizer_cov_store8";
const char SanCovStore16[] = "__sanitizer_cov_store16";
const char SanCovTraceDiv4[] = "__sanitizer_cov_trace_div4";
const char SanCovTraceDiv8[] = "__sanitizer_cov_trace_div8";
const char SanCovTraceGep[] = "__sanitizer_cov_trace_gep";
const char SanCovTraceSwitchName[] = "__sanitizer_cov_trace_switch";
const char SanCovModuleCtorTracePcGuardName[] =
    "sancov.module_ctor_trace_pc_guard";
const char SanCovModuleCtor8bitCountersName[] =
    "sancov.module_ctor_8bit_counters";
const char SanCovModuleCtorBoolFlagName[] = "sancov.module_ctor_bool_flag";
static const uint64_t SanCtorAndDtorPriority = 2;

const char SanCovTracePCGuardName[] = "__sanitizer_cov_trace_pc_guard";
const char SanCovTracePCGuardInitName[] = "__sanitizer_cov_trace_pc_guard_init";
const char SanCov8bitCountersInitName[] = "__sanitizer_cov_8bit_counters_init";
const char SanCovBoolFlagInitName[] = "__sanitizer_cov_bool_flag_init";
const char SanCovPCsInitName[] = "__sanitizer_cov_pcs_init";

const char SanCovGuardsSectionName[] = "sancov_guards";
const char SanCovCountersSectionName[] = "sancov_cntrs";
const char SanCovBoolFlagSectionName[] = "sancov_bools";
const char SanCovPCsSectionName[] = "sancov_pcs";

const char SanCovLowestStackName[] = "__sancov_lowest_stack";

// static cl::opt<int> ClCoverageLevel(
//     "sanitizer-coverage-level",
//     cl::desc("Sanitizer Coverage. 0: none, 1: entry block, 2: all blocks, "
//              "3: all blocks and critical edges"),
//     cl::Hidden, cl::init(0));
// 
// static cl::opt<bool> ClTracePC("sanitizer-coverage-trace-pc",
//                                cl::desc("Experimental pc tracing"), cl::Hidden,
//                                cl::init(false));
// 
// static cl::opt<bool> ClTracePCGuard("sanitizer-coverage-trace-pc-guard",
//                                     cl::desc("pc tracing with a guard"),
//                                     cl::Hidden, cl::init(false));
// 
// // If true, we create a global variable that contains PCs of all instrumented
// // BBs, put this global into a named section, and pass this section's bounds
// // to __sanitizer_cov_pcs_init.
// // This way the coverage instrumentation does not need to acquire the PCs
// // at run-time. Works with trace-pc-guard, inline-8bit-counters, and
// // inline-bool-flag.
// static cl::opt<bool> ClCreatePCTable("sanitizer-coverage-pc-table",
//                                      cl::desc("create a static PC table"),
//                                      cl::Hidden, cl::init(false));
// 
// static cl::opt<bool>
//     ClInline8bitCounters("sanitizer-coverage-inline-8bit-counters",
//                          cl::desc("increments 8-bit counter for every edge"),
//                          cl::Hidden, cl::init(false));
// 
// static cl::opt<bool>
//     ClInlineBoolFlag("sanitizer-coverage-inline-bool-flag",
//                      cl::desc("sets a boolean flag for every edge"), cl::Hidden,
//                      cl::init(false));
// 
// static cl::opt<bool>
//     ClCMPTracing("sanitizer-coverage-trace-compares",
//                  cl::desc("Tracing of CMP and similar instructions"),
//                  cl::Hidden, cl::init(false));
// 
// static cl::opt<bool> ClDIVTracing("sanitizer-coverage-trace-divs",
//                                   cl::desc("Tracing of DIV instructions"),
//                                   cl::Hidden, cl::init(false));
// 
// static cl::opt<bool> ClLoadTracing("sanitizer-coverage-trace-loads",
//                                    cl::desc("Tracing of load instructions"),
//                                    cl::Hidden, cl::init(false));
// 
// static cl::opt<bool> ClStoreTracing("sanitizer-coverage-trace-stores",
//                                     cl::desc("Tracing of store instructions"),
//                                     cl::Hidden, cl::init(false));
// 
// static cl::opt<bool> ClGEPTracing("sanitizer-coverage-trace-geps",
//                                   cl::desc("Tracing of GEP instructions"),
//                                   cl::Hidden, cl::init(false));
// 
// static cl::opt<bool>
//     ClPruneBlocks("sanitizer-coverage-prune-blocks",
//                   cl::desc("Reduce the number of instrumented blocks"),
//                   cl::Hidden, cl::init(true));
// 
// static cl::opt<bool> ClStackDepth("sanitizer-coverage-stack-depth",
//                                   cl::desc("max stack depth tracing"),
//                                   cl::Hidden, cl::init(false));

namespace llvm {
  void initializeModuleSanitizerCoverageCFGLegacyPassPass(PassRegistry &PB);
}

namespace {

typedef struct BBInfo {
  BasicBlock               *ptr;
  uint32_t                  blockID;
  std::vector<std::string>  calledFuncsNames;
  std::vector<BasicBlock *> successorBBptrs;
  std::vector<uint32_t>     instrumentedInstrsIDs;
  uint32_t                  numIndirectFunctionCalls;
} BBInfo;

SanitizerCoverageOptions getOptions(int LegacyCoverageLevel) {
  SanitizerCoverageOptions Res;
  switch (LegacyCoverageLevel) {
  case 0:
    Res.CoverageType = SanitizerCoverageOptions::SCK_None;
    break;
  case 1:
    Res.CoverageType = SanitizerCoverageOptions::SCK_Function;
    break;
  case 2:
    Res.CoverageType = SanitizerCoverageOptions::SCK_BB;
    break;
  case 3:
    Res.CoverageType = SanitizerCoverageOptions::SCK_Edge;
    break;
  case 4:
    Res.CoverageType = SanitizerCoverageOptions::SCK_Edge;
    Res.IndirectCalls = true;
    break;
  }
  return Res;
}

SanitizerCoverageOptions OverrideFromCL(SanitizerCoverageOptions Options) {
  // Sets CoverageType and IndirectCalls.
//  SanitizerCoverageOptions CLOpts = getOptions(ClCoverageLevel);
//  Options.CoverageType = std::max(Options.CoverageType, CLOpts.CoverageType);
//  Options.IndirectCalls |= CLOpts.IndirectCalls;
//  Options.TraceCmp |= ClCMPTracing;
//  Options.TraceDiv |= ClDIVTracing;
//  Options.TraceGep |= ClGEPTracing;
//  Options.TracePC |= ClTracePC;
//  Options.TracePCGuard |= ClTracePCGuard;
//  Options.Inline8bitCounters |= ClInline8bitCounters;
//  Options.InlineBoolFlag |= ClInlineBoolFlag;
//  Options.PCTable |= ClCreatePCTable;
//  Options.NoPrune |= !ClPruneBlocks;
//  Options.StackDepth |= ClStackDepth;
//  Options.TraceLoads |= ClLoadTracing;
//  Options.TraceStores |= ClStoreTracing;
//  if (!Options.TracePCGuard && !Options.TracePC &&
//      !Options.Inline8bitCounters && !Options.StackDepth &&
//      !Options.InlineBoolFlag && !Options.TraceLoads && !Options.TraceStores)
//    Options.TracePCGuard = true; // TracePCGuard is default.
  return Options;
}

using DomTreeCallback = function_ref<const DominatorTree *(Function &F)>;
using PostDomTreeCallback =
    function_ref<const PostDominatorTree *(Function &F)>;

class ModuleSanitizerCoverageCFG: public PassInfoMixin<ModuleSanitizerCoverageCFG>  {
public:
  ModuleSanitizerCoverageCFG(
      const SanitizerCoverageOptions &Options = SanitizerCoverageOptions(),
      const SpecialCaseList *Allowlist = nullptr,
      const SpecialCaseList *Blocklist = nullptr)
      : Options(OverrideFromCL(Options)), Allowlist(Allowlist),
        Blocklist(Blocklist) {}
  bool instrumentModule(Module &M, DomTreeCallback DTCallback,
                        PostDomTreeCallback PDTCallback);
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);

private:
  void dumpCFGtoFile(Module &m);
  bool WillInstrumentFunction(Function &F, bool allowExternal, bool printReason);
  void instrumentFunction(std::string ModuleName, Function &F, DomTreeCallback DTCallback,
                          PostDomTreeCallback PDTCallback);
  void InjectCoverageForIndirectCalls(Function &F,
                                      ArrayRef<Instruction *> IndirCalls);
  void InjectTraceForCmp(Function &F, ArrayRef<Instruction *> CmpTraceTargets);
  void InjectTraceForDiv(Function &F,
                         ArrayRef<BinaryOperator *> DivTraceTargets);
  void InjectTraceForGep(Function &F,
                         ArrayRef<GetElementPtrInst *> GepTraceTargets);
  void InjectTraceForLoadsAndStores(Function &F, ArrayRef<LoadInst *> Loads,
                                    ArrayRef<StoreInst *> Stores);
  void InjectTraceForSwitch(Function &F,
                            ArrayRef<Instruction *> SwitchTraceTargets);
  bool InjectCoverage(Function &F, ArrayRef<BasicBlock *> AllBlocks,
                      std::unordered_map<BasicBlock *, BBInfo> &infoForBBat,
                      bool IsLeafFunc = true);
  GlobalVariable *CreateFunctionLocalArrayInSection(size_t NumElements,
                                                    Function &F, Type *Ty,
                                                    const char *Section);
  GlobalVariable *CreatePCArray(Function &F, ArrayRef<BasicBlock *> AllBlocks);
  void CreateFunctionLocalArrays(Function &F, ArrayRef<BasicBlock *> AllBlocks);
  void InjectCoverageAtBlock(Function &F, BasicBlock &BB, size_t Idx,
                             bool IsLeafFunc = true);
  Function *CreateInitCallsForSections(Module &M, const char *CtorName,
                                       const char *InitFunctionName, Type *Ty,
                                       const char *Section);
  std::pair<Value *, Value *> CreateSecStartEnd(Module &M, const char *Section,
                                                Type *Ty);

  void SetNoSanitizeMetadata(Instruction *I) {
    I->setMetadata(I->getModule()->getMDKindID("nosanitize"),
                   MDNode::get(*C, None));
  }

  std::string getSectionName(const std::string &Section) const;
  std::string getSectionStart(const std::string &Section) const;
  std::string getSectionEnd(const std::string &Section) const;
  FunctionCallee SanCovTracePCIndir;
  FunctionCallee SanCovTracePC, SanCovTracePCGuard;
  std::array<FunctionCallee, 4> SanCovTraceCmpFunction;
  std::array<FunctionCallee, 4> SanCovTraceConstCmpFunction;
  std::array<FunctionCallee, 5> SanCovLoadFunction;
  std::array<FunctionCallee, 5> SanCovStoreFunction;
  std::array<FunctionCallee, 2> SanCovTraceDivFunction;
  FunctionCallee SanCovTraceGepFunction;
  FunctionCallee SanCovTraceSwitchFunction;
  GlobalVariable *SanCovLowestStack;
  Type *Int128PtrTy, *IntptrTy, *IntptrPtrTy, *Int64Ty, *Int64PtrTy, *Int32Ty,
      *Int32PtrTy, *Int16PtrTy, *Int16Ty, *Int8Ty, *Int8PtrTy, *Int1Ty,
      *Int1PtrTy;
  Module *CurModule;
  std::string CurModuleUniqueId;
  Triple TargetTriple;
  LLVMContext *C;
  const DataLayout *DL;

  GlobalVariable *FunctionGuardArray;  // for trace-pc-guard.
  GlobalVariable *Function8bitCounterArray;  // for inline-8bit-counters.
  GlobalVariable *FunctionBoolArray;         // for inline-bool-flag.
  GlobalVariable *FunctionPCsArray;  // for pc-table.
  SmallVector<GlobalValue *, 20> GlobalsToAppendToUsed;
  SmallVector<GlobalValue *, 20> GlobalsToAppendToCompilerUsed;

  SanitizerCoverageOptions Options;

  const SpecialCaseList *Allowlist;
  const SpecialCaseList *Blocklist;

  int debug = 0;
  uint32_t CurrentCoverageIndex = 0; 
  std::unordered_map<std::string, std::vector<BBInfo>> bbInfosForFunctionNamed;
};

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {

    return {LLVM_PLUGIN_API_VERSION, "SanitizerCoverageCFG", "v0.1",
          /* lambda to insert our pass into the pass pipeline. */
          [](PassBuilder &PB) {

#if LLVM_VERSION_MAJOR <= 13
            using OptimizationLevel = typename PassBuilder::OptimizationLevel;
#endif
#if LLVM_VERSION_MAJOR >= 16
            PB.registerFullLinkTimeOptimizationLastEPCallback(
#else
            PB.registerOptimizerLastEPCallback(
#endif
                [](ModulePassManager &MPM, OptimizationLevel OL) {

                  MPM.addPass(ModuleSanitizerCoverageCFG());

                });

          }};

}

class ModuleSanitizerCoverageCFGLegacyPass : public ModulePass {
public:
  ModuleSanitizerCoverageCFGLegacyPass(
      const SanitizerCoverageOptions &Options = SanitizerCoverageOptions(),
      const std::vector<std::string> &AllowlistFiles =
          std::vector<std::string>(),
      const std::vector<std::string> &BlocklistFiles =
          std::vector<std::string>())
      : ModulePass(ID), Options(Options) {
    if (AllowlistFiles.size() > 0)
      Allowlist = SpecialCaseList::createOrDie(AllowlistFiles,
                                               *vfs::getRealFileSystem());
    if (BlocklistFiles.size() > 0)
      Blocklist = SpecialCaseList::createOrDie(BlocklistFiles,
                                               *vfs::getRealFileSystem());
    initializeModuleSanitizerCoverageCFGLegacyPassPass(
        *PassRegistry::getPassRegistry());
  }
  bool runOnModule(Module &M) override {
    Options.TracePCGuard = 1;
    Options.TraceCmp = 1;
    Options.NoPrune = 1;
    Options.CoverageType = SanitizerCoverageOptions::SCK_Edge;
    Options.IndirectCalls = true;
    ModuleSanitizerCoverageCFG ModuleSancov(Options, Allowlist.get(),
                                         Blocklist.get());
    auto DTCallback = [this](Function &F) -> const DominatorTree * {
      return &this->getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
    };
    auto PDTCallback = [this](Function &F) -> const PostDominatorTree * {
      return &this->getAnalysis<PostDominatorTreeWrapperPass>(F)
                  .getPostDomTree();
    };
    return ModuleSancov.instrumentModule(M, DTCallback, PDTCallback);
  }

  static char ID; // Pass identification, replacement for typeid
  StringRef getPassName() const override { return "DBFuzzCustomSanitizerCoverage"; }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<PostDominatorTreeWrapperPass>();
  }

private:
  SanitizerCoverageOptions Options;

  std::unique_ptr<SpecialCaseList> Allowlist;
  std::unique_ptr<SpecialCaseList> Blocklist;
};

} // namespace

PreservedAnalyses ModuleSanitizerCoverageCFG::run(Module                &M,
                                                  ModuleAnalysisManager &MAM) {

  Options.TracePCGuard = 1;
  Options.TraceCmp = 1;
  Options.NoPrune = 1;
  Options.CoverageType = SanitizerCoverageOptions::SCK_Edge;
  Options.IndirectCalls = true;
  ModuleSanitizerCoverageCFG ModuleSancov(Options);
  auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  auto  DTCallback = [&FAM](Function &F) -> const DominatorTree  *{

    return &FAM.getResult<DominatorTreeAnalysis>(F);

  };

  auto PDTCallback = [&FAM](Function &F) -> const PostDominatorTree * {

    return &FAM.getResult<PostDominatorTreeAnalysis>(F);

  };

  if (ModuleSancov.instrumentModule(M, DTCallback, PDTCallback))
    return PreservedAnalyses::none();

  return PreservedAnalyses::all();

}

std::pair<Value *, Value *>
ModuleSanitizerCoverageCFG::CreateSecStartEnd(Module &M, const char *Section,
                                           Type *Ty) {
  // Use ExternalWeak so that if all sections are discarded due to section
  // garbage collection, the linker will not report undefined symbol errors.
  // Windows defines the start/stop symbols in compiler-rt so no need for
  // ExternalWeak.
  GlobalValue::LinkageTypes Linkage = TargetTriple.isOSBinFormatCOFF()
                                          ? GlobalVariable::ExternalLinkage
                                          : GlobalVariable::ExternalWeakLinkage;
  GlobalVariable *SecStart =
      new GlobalVariable(M, Ty, false, Linkage, nullptr,
                         getSectionStart(Section));
  SecStart->setVisibility(GlobalValue::HiddenVisibility);
  GlobalVariable *SecEnd =
      new GlobalVariable(M, Ty, false, Linkage, nullptr,
                         getSectionEnd(Section));
  SecEnd->setVisibility(GlobalValue::HiddenVisibility);
  IRBuilder<> IRB(M.getContext());
  if (!TargetTriple.isOSBinFormatCOFF())
    return std::make_pair(SecStart, SecEnd);

  // Account for the fact that on windows-msvc __start_* symbols actually
  // point to a uint64_t before the start of the array.
  auto SecStartI8Ptr = IRB.CreatePointerCast(SecStart, Int8PtrTy);
  auto GEP = IRB.CreateGEP(Int8Ty, SecStartI8Ptr,
                           ConstantInt::get(IntptrTy, sizeof(uint64_t)));
  return std::make_pair(IRB.CreatePointerCast(GEP, PointerType::getUnqual(Ty)),
                        SecEnd);
}

Function *ModuleSanitizerCoverageCFG::CreateInitCallsForSections(
    Module &M, const char *CtorName, const char *InitFunctionName, Type *Ty,
    const char *Section) {
  auto SecStartEnd = CreateSecStartEnd(M, Section, Ty);
  auto SecStart = SecStartEnd.first;
  auto SecEnd = SecStartEnd.second;
  Function *CtorFunc;
  Type *PtrTy = PointerType::getUnqual(Ty);
  std::tie(CtorFunc, std::ignore) = createSanitizerCtorAndInitFunctions(
      M, CtorName, InitFunctionName, {PtrTy, PtrTy}, {SecStart, SecEnd});
  assert(CtorFunc->getName() == CtorName);

  if (TargetTriple.supportsCOMDAT()) {
    // Use comdat to dedup CtorFunc.
    CtorFunc->setComdat(M.getOrInsertComdat(CtorName));
    appendToGlobalCtors(M, CtorFunc, SanCtorAndDtorPriority, CtorFunc);
  } else {
    appendToGlobalCtors(M, CtorFunc, SanCtorAndDtorPriority);
  }

  if (TargetTriple.isOSBinFormatCOFF()) {
    // In COFF files, if the contructors are set as COMDAT (they are because
    // COFF supports COMDAT) and the linker flag /OPT:REF (strip unreferenced
    // functions and data) is used, the constructors get stripped. To prevent
    // this, give the constructors weak ODR linkage and ensure the linker knows
    // to include the sancov constructor. This way the linker can deduplicate
    // the constructors but always leave one copy.
    CtorFunc->setLinkage(GlobalValue::WeakODRLinkage);
  }
  return CtorFunc;
}

bool acquireLock(const char* lockfile_path) {
    int fd = open(lockfile_path, O_CREAT | O_RDWR, 0666);
    if (fd == -1) {
        std::cerr << "Failed to open or create lock file." << std::endl;
        return false;
    }

    int attempts = 0, max_attempts = 1000;
    int delay_ms = 10, max_delay_ms = 2000;

    // Seed the random number generator
    std::srand(std::time(nullptr));

    while (attempts < max_attempts) {
        // Attempt to acquire the lock
        if (flock(fd, LOCK_EX | LOCK_NB) == 0) {
            std::cout << "Lock acquired successfully.\n";
            return true; // Lock acquired
        }

        // Lock not acquired, calculate next delay with jitter
        int jitter = std::rand() % delay_ms; // Random jitter
        if (delay_ms >= max_delay_ms) {
            delay_ms = max_delay_ms / 2 + jitter;
	} else {
            delay_ms = std::min(delay_ms + jitter, max_delay_ms);
	}

        std::this_thread::sleep_for(std::chrono::milliseconds(delay_ms));
        attempts++;
    }

    std::cerr << "Failed to acquire lock after " << max_attempts << " attempts." << std::endl;
    close(fd);
    return false;
}

// Function to release the lock
void releaseLock(const char *lockFilePath) {
    flock(open(lockFilePath, O_RDWR), LOCK_UN);
}

void ModuleSanitizerCoverageCFG::dumpCFGtoFile(Module &M) {
  char *cfg_path = getenv("AFL_LLVM_CFG_FILE");
  bool have_path = cfg_path != NULL;

  if (!have_path) {
    if (debug) fprintf(stderr, "No file to store CFG specified with AFL_LLVM_CFG_FILE env\n");
    return;
  } else {
    if (debug) fprintf(stderr, "Storing CFG to %s\n", cfg_path);
  }

  // Open the binary file for reading in binary mode
  std::ifstream file(cfg_path, std::ios::binary);

  uint32_t initial_function_count = 0;
  if (file.is_open()) {
    std::streampos fsize = file.tellg();
    file.seekg(0, std::ios::end);
    fsize = file.tellg() - fsize;
    file.seekg(0, std::ios::beg);
    
    if (fsize >= 8) {
      // Read the first 4 bytes into a buffer
      unsigned char buffer[8];
      file.read(reinterpret_cast<char*>(buffer), sizeof(buffer));

      initial_function_count = (static_cast<uint32_t>(buffer[4]) << 24) |
                               (static_cast<uint32_t>(buffer[5]) << 16) |
                               (static_cast<uint32_t>(buffer[6]) << 8) |
                               static_cast<uint32_t>(buffer[7]);

    } else {
      if (debug) 
        fprintf(stderr, 
		"CFG file %s was empty (%s - %s)\n", 
		cfg_path, 
		M.getName().str().c_str(), 
		M.getSourceFileName().c_str());
    }

    file.close();
  } else {
    fprintf(stderr, "Failed to open CFG file %s after calcing - do have the lock (%s - %s)\n", cfg_path, M.getName().str().c_str(), M.getSourceFileName().c_str());
    assert(0);
  }

  std::vector<uint8_t> serialisedCFG;

#define SERIALIZE_U32(value) \
  serialisedCFG.push_back(static_cast<uint8_t>(value >> 24)); \
  serialisedCFG.push_back(static_cast<uint8_t>(value >> 16)); \
  serialisedCFG.push_back(static_cast<uint8_t>(value >> 8)); \
  serialisedCFG.push_back(static_cast<uint8_t>(value)); 
#define SERIALIZE_PTR(ptr) \
  uintptr_t _bytePtr = reinterpret_cast<uintptr_t>(ptr); \
  for (size_t i = 0; i < sizeof(_bytePtr); ++i) { \
    serialisedCFG.push_back(_bytePtr & 0xFF); \
    _bytePtr >>= 8; \
  }

  for (const auto &pair: bbInfosForFunctionNamed) {
    std::string fname = pair.first;
    std::vector<BBInfo> bbInfos = pair.second;

    SERIALIZE_U32(fname.size());
    serialisedCFG.insert(serialisedCFG.end(), fname.begin(), fname.end());
    SERIALIZE_U32(static_cast<uint32_t>(bbInfos.size()));
  
    for (BBInfo &bbInfo: bbInfos) {
      SERIALIZE_PTR(bbInfo.ptr);
      // uint32_t cov_map_idx = (bbInfo.blockID == UINT32_MAX) ? UINT32_MAX : bbInfo.blockID + coverage_index_offset;
      SERIALIZE_U32(bbInfo.blockID);
      SERIALIZE_U32(bbInfo.numIndirectFunctionCalls);

      SERIALIZE_U32(static_cast<uint32_t>(bbInfo.calledFuncsNames.size()));
      for (auto called: bbInfo.calledFuncsNames) {
        SERIALIZE_U32(static_cast<uint32_t>(called.size()));
        serialisedCFG.insert(serialisedCFG.end(), called.begin(), called.end());
      }

      SERIALIZE_U32(static_cast<uint32_t>(bbInfo.successorBBptrs.size()));
      for (auto bbPtr: bbInfo.successorBBptrs) {
        SERIALIZE_PTR(bbPtr);
      }

      SERIALIZE_U32(static_cast<uint32_t>(bbInfo.instrumentedInstrsIDs.size()));
      for (auto instrID: bbInfo.instrumentedInstrsIDs) {
        SERIALIZE_U32(instrID);
      }
    }
  }

  if (debug) fprintf(stderr, "Serialised total length of CFG: %zu\n", serialisedCFG.size());

#undef SERIALIZE_U32
#undef SERIALIZE_PTR

  std::ofstream outfile(cfg_path, std::ios::in | std::ios::binary);
  if (outfile.is_open()) {
      // Get the current size of the file
      outfile.seekp(0, std::ios::beg);
      uint8_t bytes[4];
      uint32_t final_coverage_index = CurrentCoverageIndex;
      bytes[0] = static_cast<uint8_t>((final_coverage_index >> 24) & 0xFF);
      bytes[1] = static_cast<uint8_t>((final_coverage_index >> 16) & 0xFF);
      bytes[2] = static_cast<uint8_t>((final_coverage_index >> 8) & 0xFF);
      bytes[3] = static_cast<uint8_t>(final_coverage_index & 0xFF);
      outfile.write(reinterpret_cast<const char*>(bytes), sizeof(bytes));

      uint32_t total_functions = initial_function_count + bbInfosForFunctionNamed.size();
      bytes[0] = static_cast<uint8_t>((total_functions >> 24) & 0xFF);
      bytes[1] = static_cast<uint8_t>((total_functions >> 16) & 0xFF);
      bytes[2] = static_cast<uint8_t>((total_functions >> 8) & 0xFF);
      bytes[3] = static_cast<uint8_t>(total_functions & 0xFF);
      outfile.write(reinterpret_cast<const char*>(bytes), sizeof(bytes));

      printf("LibAFL: Instrumented %u blocks, final coverage index: %u\n", 
             CurrentCoverageIndex,
             final_coverage_index);

      outfile.seekp(0, std::ios::end);
      outfile.write(reinterpret_cast<const char*>(serialisedCFG.data()), serialisedCFG.size());
      outfile.close();
  } else {
      // Check for specific error conditions
      if (outfile.fail()) {
        std::cerr << "Reason: Failed to open file (e.g., file not found, permission denied)." << std::endl;
      } else if (outfile.bad()) {
        std::cerr << "Reason: Fatal error occurred while attempting to open file." << std::endl;
      }
      std::cerr << "Error opening file at AFL_LLVM_CFG_FILE: " << cfg_path << 
	     ". Make sure you create it before compiling (`touch $AFL_LLVM_CFG_FILE`)" 
	     << std::endl;
      assert(0);
  }

  char lock_file_path[1048];
  memcpy(lock_file_path, cfg_path, strlen(cfg_path));
  memcpy(lock_file_path + strlen(cfg_path), ".lock", strlen(".lock") + 1);
  releaseLock(lock_file_path);
  if (debug) fprintf(stderr, "Released lock on %s\n", lock_file_path);
}

bool ModuleSanitizerCoverageCFG::instrumentModule(
    Module &M, DomTreeCallback DTCallback, PostDomTreeCallback PDTCallback) {
  
  debug = getenv("AFL_DEBUG") == NULL ? 0 : 1;

  char *cfg_path = getenv("AFL_LLVM_CFG_FILE");
  if (cfg_path != NULL) {

    char lock_file_path[1048];
    memcpy(lock_file_path, cfg_path, strlen(cfg_path));
    memcpy(lock_file_path + strlen(cfg_path), ".lock", strlen(".lock") + 1);

    if (debug) fprintf(stderr, "Attempting to acquire lock on %s\n", lock_file_path);
    bool lock_acquired = acquireLock(lock_file_path);
    if (!lock_acquired) {
      fprintf(stderr, "Failed to acquire lock on CFG file (%s - %s)\n", M.getName().str().c_str(), M.getSourceFileName().c_str());
      assert(0 && "Failed to acquire lock on CFG file");
    }

    // Open the binary file for reading in binary mode
    std::ifstream file(cfg_path, std::ios::binary);

    uint32_t coverage_index_offset = 0, initial_function_count = 0;
    if (file.is_open()) {
      std::streampos fsize = file.tellg();
      file.seekg(0, std::ios::end);
      fsize = file.tellg() - fsize;
      file.seekg(0, std::ios::beg);
      
      if (fsize >= 8) {
        // Read the first 4 bytes into a buffer
        unsigned char buffer[8];
        file.read(reinterpret_cast<char*>(buffer), sizeof(buffer));

        // Combine the bytes into a uint32_t
        CurrentCoverageIndex = (static_cast<uint32_t>(buffer[0]) << 24) |
                                (static_cast<uint32_t>(buffer[1]) << 16) |
                                (static_cast<uint32_t>(buffer[2]) << 8) |
                                static_cast<uint32_t>(buffer[3]);
        initial_function_count = (static_cast<uint32_t>(buffer[4]) << 24) |
                                 (static_cast<uint32_t>(buffer[5]) << 16) |
                                 (static_cast<uint32_t>(buffer[6]) << 8) |
                                 static_cast<uint32_t>(buffer[7]);

        if (debug) fprintf(stderr, "Set the Starting Coverage Index to %u (there were %u functions)\n", CurrentCoverageIndex, initial_function_count);
      } else {
        if (debug) fprintf(stderr, "File %s was empty\n", cfg_path);
      }

      file.close();
    } else {
      fprintf(stderr, "Failed to open CFG file %s (%s - %s) error %d\n", cfg_path, M.getName().str().c_str(), M.getSourceFileName().c_str(), std::strerror(errno));
      assert(0);
    }
  } else {
    if (debug) fprintf(stderr, "No CFG_FILE!\n");
  }


  if (Options.CoverageType == SanitizerCoverageOptions::SCK_None) {
    fprintf(stderr, "Coverage level was SCK_None, bailing\n");
    assert(0);
    return false;
  }
  if (Allowlist &&
      !Allowlist->inSection("coverage", "src", M.getSourceFileName()))
    return false;
  if (Blocklist &&
      Blocklist->inSection("coverage", "src", M.getSourceFileName()))
    return false;
  C = &(M.getContext());
  DL = &M.getDataLayout();
  CurModule = &M;
  CurModuleUniqueId = getUniqueModuleId(CurModule);
  TargetTriple = Triple(M.getTargetTriple());
  FunctionGuardArray = nullptr;
  Function8bitCounterArray = nullptr;
  FunctionBoolArray = nullptr;
  FunctionPCsArray = nullptr;
  IntptrTy = Type::getIntNTy(*C, DL->getPointerSizeInBits());
  IntptrPtrTy = PointerType::getUnqual(IntptrTy);
  Type *VoidTy = Type::getVoidTy(*C);
  IRBuilder<> IRB(*C);
  Int128PtrTy = PointerType::getUnqual(IRB.getInt128Ty());
  Int64PtrTy = PointerType::getUnqual(IRB.getInt64Ty());
  Int16PtrTy = PointerType::getUnqual(IRB.getInt16Ty());
  Int32PtrTy = PointerType::getUnqual(IRB.getInt32Ty());
  Int8PtrTy = PointerType::getUnqual(IRB.getInt8Ty());
  Int1PtrTy = PointerType::getUnqual(IRB.getInt1Ty());
  Int64Ty = IRB.getInt64Ty();
  Int32Ty = IRB.getInt32Ty();
  Int16Ty = IRB.getInt16Ty();
  Int8Ty = IRB.getInt8Ty();
  Int1Ty = IRB.getInt1Ty();

  SanCovTracePCIndir =
      M.getOrInsertFunction(SanCovTracePCIndirName, VoidTy, IntptrTy);
  // Make sure smaller parameters are zero-extended to i64 if required by the
  // target ABI.
  AttributeList SanCovTraceCmpZeroExtAL;
  SanCovTraceCmpZeroExtAL =
      SanCovTraceCmpZeroExtAL.addParamAttribute(*C, 0, Attribute::ZExt);
  SanCovTraceCmpZeroExtAL =
      SanCovTraceCmpZeroExtAL.addParamAttribute(*C, 1, Attribute::ZExt);

  SanCovTraceCmpFunction[0] =
      M.getOrInsertFunction(SanCovTraceCmp1, SanCovTraceCmpZeroExtAL, VoidTy,
                            IRB.getInt8Ty(), IRB.getInt8Ty());
  SanCovTraceCmpFunction[1] =
      M.getOrInsertFunction(SanCovTraceCmp2, SanCovTraceCmpZeroExtAL, VoidTy,
                            IRB.getInt16Ty(), IRB.getInt16Ty());
  SanCovTraceCmpFunction[2] =
      M.getOrInsertFunction(SanCovTraceCmp4, SanCovTraceCmpZeroExtAL, VoidTy,
                            IRB.getInt32Ty(), IRB.getInt32Ty());
  SanCovTraceCmpFunction[3] =
      M.getOrInsertFunction(SanCovTraceCmp8, VoidTy, Int64Ty, Int64Ty);

  SanCovTraceConstCmpFunction[0] = M.getOrInsertFunction(
      SanCovTraceConstCmp1, SanCovTraceCmpZeroExtAL, VoidTy, Int8Ty, Int8Ty);
  SanCovTraceConstCmpFunction[1] = M.getOrInsertFunction(
      SanCovTraceConstCmp2, SanCovTraceCmpZeroExtAL, VoidTy, Int16Ty, Int16Ty);
  SanCovTraceConstCmpFunction[2] = M.getOrInsertFunction(
      SanCovTraceConstCmp4, SanCovTraceCmpZeroExtAL, VoidTy, Int32Ty, Int32Ty);
  SanCovTraceConstCmpFunction[3] =
      M.getOrInsertFunction(SanCovTraceConstCmp8, VoidTy, Int64Ty, Int64Ty);

  // Loads.
  SanCovLoadFunction[0] = M.getOrInsertFunction(SanCovLoad1, VoidTy, Int8PtrTy);
  SanCovLoadFunction[1] =
      M.getOrInsertFunction(SanCovLoad2, VoidTy, Int16PtrTy);
  SanCovLoadFunction[2] =
      M.getOrInsertFunction(SanCovLoad4, VoidTy, Int32PtrTy);
  SanCovLoadFunction[3] =
      M.getOrInsertFunction(SanCovLoad8, VoidTy, Int64PtrTy);
  SanCovLoadFunction[4] =
      M.getOrInsertFunction(SanCovLoad16, VoidTy, Int128PtrTy);
  // Stores.
  SanCovStoreFunction[0] =
      M.getOrInsertFunction(SanCovStore1, VoidTy, Int8PtrTy);
  SanCovStoreFunction[1] =
      M.getOrInsertFunction(SanCovStore2, VoidTy, Int16PtrTy);
  SanCovStoreFunction[2] =
      M.getOrInsertFunction(SanCovStore4, VoidTy, Int32PtrTy);
  SanCovStoreFunction[3] =
      M.getOrInsertFunction(SanCovStore8, VoidTy, Int64PtrTy);
  SanCovStoreFunction[4] =
      M.getOrInsertFunction(SanCovStore16, VoidTy, Int128PtrTy);

  {
    AttributeList AL;
    AL = AL.addParamAttribute(*C, 0, Attribute::ZExt);
    SanCovTraceDivFunction[0] =
        M.getOrInsertFunction(SanCovTraceDiv4, AL, VoidTy, IRB.getInt32Ty());
  }
  SanCovTraceDivFunction[1] =
      M.getOrInsertFunction(SanCovTraceDiv8, VoidTy, Int64Ty);
  SanCovTraceGepFunction =
      M.getOrInsertFunction(SanCovTraceGep, VoidTy, IntptrTy);
  SanCovTraceSwitchFunction =
      M.getOrInsertFunction(SanCovTraceSwitchName, VoidTy, Int64Ty, Int64PtrTy);

  Constant *SanCovLowestStackConstant =
      M.getOrInsertGlobal(SanCovLowestStackName, IntptrTy);
  SanCovLowestStack = dyn_cast<GlobalVariable>(SanCovLowestStackConstant);
  if (!SanCovLowestStack || SanCovLowestStack->getValueType() != IntptrTy) {
    C->emitError(StringRef("'") + SanCovLowestStackName +
                 "' should not be declared by the user");
    return true;
  }
  SanCovLowestStack->setThreadLocalMode(
      GlobalValue::ThreadLocalMode::InitialExecTLSModel);
  if (Options.StackDepth && !SanCovLowestStack->isDeclaration())
    SanCovLowestStack->setInitializer(Constant::getAllOnesValue(IntptrTy));

  SanCovTracePC = M.getOrInsertFunction(SanCovTracePCName, VoidTy);
  SanCovTracePCGuard =
      M.getOrInsertFunction(SanCovTracePCGuardName, VoidTy, Int32PtrTy);

  auto moduleName = M.getName().str();
  for (auto &F : M)
    instrumentFunction(moduleName, F, DTCallback, PDTCallback);

  Function *Ctor = nullptr;

  if (FunctionGuardArray)
    Ctor = CreateInitCallsForSections(M, SanCovModuleCtorTracePcGuardName,
                                      SanCovTracePCGuardInitName, Int32Ty,
                                      SanCovGuardsSectionName);
  if (Function8bitCounterArray)
    Ctor = CreateInitCallsForSections(M, SanCovModuleCtor8bitCountersName,
                                      SanCov8bitCountersInitName, Int8Ty,
                                      SanCovCountersSectionName);
  if (FunctionBoolArray) {
    Ctor = CreateInitCallsForSections(M, SanCovModuleCtorBoolFlagName,
                                      SanCovBoolFlagInitName, Int1Ty,
                                      SanCovBoolFlagSectionName);
  }
  if (Ctor && Options.PCTable) {
    auto SecStartEnd = CreateSecStartEnd(M, SanCovPCsSectionName, IntptrTy);
    FunctionCallee InitFunction = declareSanitizerInitFunction(
        M, SanCovPCsInitName, {IntptrPtrTy, IntptrPtrTy});
    IRBuilder<> IRBCtor(Ctor->getEntryBlock().getTerminator());
    IRBCtor.CreateCall(InitFunction, {SecStartEnd.first, SecStartEnd.second});
  }
  appendToUsed(M, GlobalsToAppendToUsed);
  appendToCompilerUsed(M, GlobalsToAppendToCompilerUsed);
  dumpCFGtoFile(M);
  return true;
}

// True if block has successors and it dominates all of them.
static bool isFullDominator(const BasicBlock *BB, const DominatorTree *DT) {
  if (succ_empty(BB))
    return false;

  return llvm::all_of(successors(BB), [&](const BasicBlock *SUCC) {
    return DT->dominates(BB, SUCC);
  });
}

// True if block has predecessors and it postdominates all of them.
static bool isFullPostDominator(const BasicBlock *BB,
                                const PostDominatorTree *PDT) {
  if (pred_empty(BB))
    return false;

  return llvm::all_of(predecessors(BB), [&](const BasicBlock *PRED) {
    return PDT->dominates(BB, PRED);
  });
}

static bool shouldInstrumentBlock(const Function &F, const BasicBlock *BB,
                                  const DominatorTree *DT,
                                  const PostDominatorTree *PDT,
                                  const SanitizerCoverageOptions &Options) {
  // Don't insert coverage for blocks containing nothing but unreachable: we
  // will never call __sanitizer_cov() for them, so counting them in
  // NumberOfInstrumentedBlocks() might complicate calculation of code coverage
  // percentage. Also, unreachable instructions frequently have no debug
  // locations.
  if (isa<UnreachableInst>(BB->getFirstNonPHIOrDbgOrLifetime()))
    return false;

  // Don't insert coverage into blocks without a valid insertion point
  // (catchswitch blocks).
  if (BB->getFirstInsertionPt() == BB->end())
    return false;

  if (Options.NoPrune || &F.getEntryBlock() == BB)
    return true;

  if (Options.CoverageType == SanitizerCoverageOptions::SCK_Function &&
      &F.getEntryBlock() != BB)
    return false;

  // Do not instrument full dominators, or full post-dominators with multiple
  // predecessors.
  return !isFullDominator(BB, DT)
    && !(isFullPostDominator(BB, PDT) && !BB->getSinglePredecessor());
}


// Returns true iff From->To is a backedge.
// A twist here is that we treat From->To as a backedge if
//   * To dominates From or
//   * To->UniqueSuccessor dominates From
static bool IsBackEdge(BasicBlock *From, BasicBlock *To,
                       const DominatorTree *DT) {
  if (DT->dominates(To, From))
    return true;
  if (auto Next = To->getUniqueSuccessor())
    if (DT->dominates(Next, From))
      return true;
  return false;
}

// Prunes uninteresting Cmp instrumentation:
//   * CMP instructions that feed into loop backedge branch.
//
// Note that Cmp pruning is controlled by the same flag as the
// BB pruning.
static bool IsInterestingCmp(ICmpInst *CMP, const DominatorTree *DT,
                             const SanitizerCoverageOptions &Options) {
  if (!Options.NoPrune)
    if (CMP->hasOneUse())
      if (auto BR = dyn_cast<BranchInst>(CMP->user_back()))
        for (BasicBlock *B : BR->successors())
          if (IsBackEdge(BR->getParent(), B, DT))
            return false;
  return true;
}

// /* Function that we never instrument or analyze */
// /* Note: this ignore check is also called in isInInstrumentList() */
// bool isIgnoreFunction(const llvm::Function *F) {

//   // Starting from "LLVMFuzzer" these are functions used in libfuzzer based
//   // fuzzing campaign installations, e.g. oss-fuzz

//   static constexpr const char *ignoreList[] = {

//       "asan.",
//       "llvm.",
//       "sancov.",
//       "__ubsan",
//       "ign.",
//       "__afl",
//       "_fini",
//       "__libc_",
//       "__asan",
//       "__msan",
//       "__cmplog",
//       "__sancov",
//       "__san",
//       "__cxx_",
//       "__decide_deferred",
//       "_GLOBAL",
//       "_ZZN6__asan",
//       "_ZZN6__lsan",
//       "msan.",
//       "LLVMFuzzerM",
//       "LLVMFuzzerC",
//       "LLVMFuzzerI",
//       "maybe_duplicate_stderr",
//       "discard_output",
//       "close_stdout",
//       "dup_and_close_stderr",
//       "maybe_close_fd_mask",
//       "ExecuteFilesOnyByOne"

//   };

//   for (auto const &ignoreListFunc : ignoreList) {

//     if (F->getName().startswith(ignoreListFunc)) { return true; }

//   }

//   static constexpr const char *ignoreSubstringList[] = {

//       "__asan",     "__msan",       "__ubsan",    "__lsan",  "__san",
//       "__sanitize", "DebugCounter", "DwarfDebug", "DebugLoc"

//   };

//   // This check is very sensitive, we must be sure to not include patterns
//   // that are part of user-written C++ functions like the ones including
//   // std::string as parameter (see #1927) as the mangled type is inserted in the
//   // mangled name of the user-written function
//   for (auto const &ignoreListFunc : ignoreSubstringList) {

//     // hexcoder: F->getName().contains() not avaiilable in llvm 3.8.0
//     if (StringRef::npos != F->getName().find(ignoreListFunc)) { return true; }

//   }

//   return false;
// }

bool ModuleSanitizerCoverageCFG::WillInstrumentFunction(Function &F, bool allowExternal, bool printReason) {
  if (!allowExternal && F.empty()) {
    if (debug && printReason) fprintf(stderr, "  won't instrument %s as it's empty\n", F.getName().str().c_str());
    return 0;
  }
  if (F.getName().find(".module_ctor") != std::string::npos) {
    if (debug && printReason) fprintf(stderr, "  won't instrument %s as it's .module_ctor\n", F.getName().str().c_str());
    return 0; // Should not instrument sanitizer init functions.
  }
  if (F.getName().startswith("__sanitizer_")) {
    if (debug && printReason) fprintf(stderr, "  won't instrument %s as it starts with __sanitizer_\n", F.getName().str().c_str());
    return 0; // Don't instrument __sanitizer_* callbacks.
  }
  // Don't touch available_externally functions, their actual body is elewhere.
  if (!allowExternal && F.getLinkage() == GlobalValue::AvailableExternallyLinkage) {
    if (debug && printReason) fprintf(stderr, "  won't instrument %s as it's available externally\n", F.getName().str().c_str());
    return 0;
  }
  // Don't instrument MSVC CRT configuration helpers. They may run before normal
  // initialization.
  if (F.getName() == "__local_stdio_printf_options" ||
      F.getName() == "__local_stdio_scanf_options") {
    if (debug && printReason) fprintf(stderr, "  won't instrument %s as it's _local_stdio\n", F.getName().str().c_str());
    return 0;
  }
  if (!F.empty() && isa<UnreachableInst>(F.getEntryBlock().getTerminator())) {
    if (debug && printReason) fprintf(stderr, "  won't instrument %s as it's unreachable\n", F.getName().str().c_str());
    return 0;
  }
  // Don't instrument functions using SEH for now. Splitting basic blocks like
  // we do for coverage breaks WinEHPrepare.
  // FIXME: Remove this when SEH no longer uses landingpad pattern matching.
  if (F.hasPersonalityFn() &&
      isAsynchronousEHPersonality(classifyEHPersonality(F.getPersonalityFn()))) {
    if (debug && printReason) fprintf(stderr, "  won't instrument %s as it's got personality\n", F.getName().str().c_str());
    return 0;
  }
  if (Allowlist && !Allowlist->inSection("coverage", "fun", F.getName())) {
    if (debug && printReason) fprintf(stderr, "  won't instrument %s as it's not in the allowlist\n", F.getName().str().c_str());
    return 0;
  }
  if (Blocklist && Blocklist->inSection("coverage", "fun", F.getName())) {
    if (debug && printReason) fprintf(stderr, "  won't instrument %s as it's in the blocklist\n", F.getName().str().c_str());
    return 0;
  }
  if (F.hasFnAttribute(Attribute::NoSanitizeCoverage)) {
    if (debug && printReason) fprintf(stderr, "  won't instrument %s as it's marked NoSanitizeCoverage\n", F.getName().str().c_str());
    return 0;
  }

  return 1;
}

void ModuleSanitizerCoverageCFG::instrumentFunction(
    std::string ModuleName,
    Function &F, DomTreeCallback DTCallback, PostDomTreeCallback PDTCallback) {
  if (!WillInstrumentFunction(F, 0, 0))
    return;
  if (Options.CoverageType >= SanitizerCoverageOptions::SCK_Edge)
    SplitAllCriticalEdges(F, CriticalEdgeSplittingOptions().setIgnoreUnreachableDests());
  SmallVector<Instruction *, 8> IndirCalls;
  SmallVector<BasicBlock *, 16> BlocksToInstrument;
  SmallVector<Instruction *, 8> CmpTraceTargets;
  SmallVector<Instruction *, 8> SwitchTraceTargets;
  SmallVector<BinaryOperator *, 8> DivTraceTargets;
  SmallVector<GetElementPtrInst *, 8> GepTraceTargets;
  SmallVector<LoadInst *, 8> Loads;
  SmallVector<StoreInst *, 8> Stores;

  if (debug) fprintf(stderr, "Instrumenting %s\n", F.getName().str().c_str());

  const DominatorTree *DT = DTCallback(F);
  const PostDominatorTree *PDT = PDTCallback(F);
  bool IsLeafFunc = true;
  std::unordered_map<BasicBlock *, BBInfo> infoForBBat;

  for (auto &BB : F) {
    BBInfo curBBinfo;
    curBBinfo.blockID = UINT32_MAX;
    curBBinfo.numIndirectFunctionCalls = 0;
    curBBinfo.ptr = &BB;

    if (shouldInstrumentBlock(F, &BB, DT, PDT, Options))
      BlocksToInstrument.push_back(&BB);
    for (auto &Inst : BB) {

      CallInst *callInst = nullptr;
      Function *Callee = nullptr;
      if ((callInst = dyn_cast<CallInst>(&Inst))) {
        if (callInst->isIndirectCall()) {
          curBBinfo.numIndirectFunctionCalls++;
        } else if ((Callee = callInst->getCalledFunction())){
          std::string FuncName = Callee->getName().str();
          if (WillInstrumentFunction(*Callee, 1, 1) && !isIgnoreFunction(Callee)) {
            if (Callee->hasInternalLinkage()) {
              FuncName = ModuleName + "::" + FuncName;
            }
            // If this function is instrumented then lets bother adding it
            if (debug) fprintf(stderr, "Adding called function %s to %p\n", FuncName.c_str(), &BB);
            curBBinfo.calledFuncsNames.push_back(FuncName);
          } else {
	          if (debug) fprintf(stderr, "Skipping called function %s\n", FuncName.c_str());
	        }
	      }
      }
      if (Options.IndirectCalls) {
        CallBase *CB = dyn_cast<CallBase>(&Inst);
        if (CB && !CB->getCalledFunction()) {
          IndirCalls.push_back(&Inst);
          curBBinfo.numIndirectFunctionCalls++;
        }
      }
      if (Options.TraceCmp) {
        if (ICmpInst *CMP = dyn_cast<ICmpInst>(&Inst))
          if (IsInterestingCmp(CMP, DT, Options))
            CmpTraceTargets.push_back(&Inst);
        if (isa<SwitchInst>(&Inst))
          SwitchTraceTargets.push_back(&Inst);
      }
      if (Options.TraceDiv)
        if (BinaryOperator *BO = dyn_cast<BinaryOperator>(&Inst))
          if (BO->getOpcode() == Instruction::SDiv ||
              BO->getOpcode() == Instruction::UDiv)
            DivTraceTargets.push_back(BO);
      if (Options.TraceGep)
        if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&Inst))
          GepTraceTargets.push_back(GEP);
      if (Options.TraceLoads)
        if (LoadInst *LI = dyn_cast<LoadInst>(&Inst))
          Loads.push_back(LI);
      if (Options.TraceStores)
        if (StoreInst *SI = dyn_cast<StoreInst>(&Inst))
          Stores.push_back(SI);
      if (Options.StackDepth)
        if (isa<InvokeInst>(Inst) ||
            (isa<CallInst>(Inst) && !isa<IntrinsicInst>(Inst)))
          IsLeafFunc = false;
    }

    infoForBBat[&BB] = curBBinfo;
  }

  InjectCoverage(F, BlocksToInstrument, infoForBBat, IsLeafFunc);
  InjectCoverageForIndirectCalls(F, IndirCalls);
  InjectTraceForCmp(F, CmpTraceTargets);
  InjectTraceForSwitch(F, SwitchTraceTargets);
  InjectTraceForDiv(F, DivTraceTargets);
  InjectTraceForGep(F, GepTraceTargets);
  InjectTraceForLoadsAndStores(F, Loads, Stores);

  for (auto &BB: F) {
    // Get the begin and end iterators for the successors of the BasicBlock
    auto succBegin = succ_begin(&BB);
    auto succEnd = succ_end(&BB);
  
    // Iterate over the successors of the BasicBlock using the iterators
    for (auto succIt = succBegin; succIt != succEnd; ++succIt) {
      BasicBlock* succ = *succIt;
      infoForBBat[&BB].successorBBptrs.push_back(succ);
    }
  }

  std::vector<BBInfo> all;
  for (const auto& pair : infoForBBat) {
    BBInfo info = pair.second;
    if (info.ptr == &F.getEntryBlock()) {
      all.insert(all.begin(), info);
    } else {
      all.push_back(info);
    }
  }
  for (auto info : all) {
    if (debug) {
      fprintf(stderr, "  { ptr: %p, id: %u, called_funcs: %lu, successors: %lu, instrumentedInstrs: %lu }\n",
        info.ptr, info.blockID, info.calledFuncsNames.size(), info.successorBBptrs.size(), info.instrumentedInstrsIDs.size());
    }
  }

  std::string FuncName = F.getName().str();
  if (F.hasInternalLinkage()) {
    FuncName = ModuleName + "::" + FuncName;
  }
  bbInfosForFunctionNamed[FuncName] = all;
}

GlobalVariable *ModuleSanitizerCoverageCFG::CreateFunctionLocalArrayInSection(
    size_t NumElements, Function &F, Type *Ty, const char *Section) {
  ArrayType *ArrayTy = ArrayType::get(Ty, NumElements);

    // Generate the sequence of constant integers
    std::vector<Constant *> ArrayValues;
    for (size_t i = 0; i < NumElements; ++i) {
        Constant *Value = ConstantInt::get(Ty, CurrentCoverageIndex++);
        ArrayValues.push_back(Value);
    }

    // Create the constant array using the generated values
    Constant *ArrayInitializer = ConstantArray::get(ArrayTy, ArrayValues);

  auto Array = new GlobalVariable(
      *CurModule, ArrayTy, false, GlobalVariable::PrivateLinkage,
      ArrayInitializer, "__sancov_gen_");
      //Constant::getNullValue(ArrayTy), "__sancov_gen_");

  if (TargetTriple.supportsCOMDAT() &&
      (TargetTriple.isOSBinFormatELF() || !F.isInterposable()))
    if (auto Comdat = getOrCreateFunctionComdat(F, TargetTriple))
      Array->setComdat(Comdat);
  Array->setSection(getSectionName(Section));
  Array->setAlignment(Align(DL->getTypeStoreSize(Ty).getFixedSize()));

  // sancov_pcs parallels the other metadata section(s). Optimizers (e.g.
  // GlobalOpt/ConstantMerge) may not discard sancov_pcs and the other
  // section(s) as a unit, so we conservatively retain all unconditionally in
  // the compiler.
  //
  // With comdat (COFF/ELF), the linker can guarantee the associated sections
  // will be retained or discarded as a unit, so llvm.compiler.used is
  // sufficient. Otherwise, conservatively make all of them retained by the
  // linker.
  if (Array->hasComdat())
    GlobalsToAppendToCompilerUsed.push_back(Array);
  else
    GlobalsToAppendToUsed.push_back(Array);

  return Array;
}

GlobalVariable *
ModuleSanitizerCoverageCFG::CreatePCArray(Function &F,
                                       ArrayRef<BasicBlock *> AllBlocks) {
  size_t N = AllBlocks.size();
  assert(N);
  SmallVector<Constant *, 32> PCs;
  IRBuilder<> IRB(&*F.getEntryBlock().getFirstInsertionPt());
  for (size_t i = 0; i < N; i++) {
    if (&F.getEntryBlock() == AllBlocks[i]) {
      PCs.push_back((Constant *)IRB.CreatePointerCast(&F, IntptrPtrTy));
      PCs.push_back((Constant *)IRB.CreateIntToPtr(
          ConstantInt::get(IntptrTy, 1), IntptrPtrTy));
    } else {
      PCs.push_back((Constant *)IRB.CreatePointerCast(
          BlockAddress::get(AllBlocks[i]), IntptrPtrTy));
      PCs.push_back((Constant *)IRB.CreateIntToPtr(
          ConstantInt::get(IntptrTy, 0), IntptrPtrTy));
    }
  }
  auto *PCArray = CreateFunctionLocalArrayInSection(N * 2, F, IntptrPtrTy,
                                                    SanCovPCsSectionName);
  PCArray->setInitializer(
      ConstantArray::get(ArrayType::get(IntptrPtrTy, N * 2), PCs));
  PCArray->setConstant(true);

  return PCArray;
}

void ModuleSanitizerCoverageCFG::CreateFunctionLocalArrays(
    Function &F, ArrayRef<BasicBlock *> AllBlocks) {
  if (Options.TracePCGuard)
    FunctionGuardArray = CreateFunctionLocalArrayInSection(
	AllBlocks.size(), F, Int32Ty, SanCovGuardsSectionName);

  if (Options.Inline8bitCounters)
    Function8bitCounterArray = CreateFunctionLocalArrayInSection(
        AllBlocks.size(), F, Int8Ty, SanCovCountersSectionName);
  if (Options.InlineBoolFlag)
    FunctionBoolArray = CreateFunctionLocalArrayInSection(
        AllBlocks.size(), F, Int1Ty, SanCovBoolFlagSectionName);

  if (Options.PCTable)
    FunctionPCsArray = CreatePCArray(F, AllBlocks);
}

bool ModuleSanitizerCoverageCFG::InjectCoverage(
  Function &F,
  ArrayRef<BasicBlock *> AllBlocks,
  std::unordered_map<BasicBlock *, BBInfo> &infoForBBat,
  bool IsLeafFunc
) {
  if (AllBlocks.empty()) return false;
  size_t CovIndex = CurrentCoverageIndex;
  CreateFunctionLocalArrays(F, AllBlocks);
  for (size_t i = 0, N = AllBlocks.size(); i < N; i++) {
    infoForBBat[AllBlocks[i]].blockID = CovIndex++;
    InjectCoverageAtBlock(F, *AllBlocks[i], i, IsLeafFunc);
  }
  assert(CovIndex == CurrentCoverageIndex);
  return true;
}

// On every indirect call we call a run-time function
// __sanitizer_cov_indir_call* with two parameters:
//   - callee address,
//   - global cache array that contains CacheSize pointers (zero-initialized).
//     The cache is used to speed up recording the caller-callee pairs.
// The address of the caller is passed implicitly via caller PC.
// CacheSize is encoded in the name of the run-time function.
void ModuleSanitizerCoverageCFG::InjectCoverageForIndirectCalls(
    Function &F, ArrayRef<Instruction *> IndirCalls) {
  if (IndirCalls.empty())
    return;
  assert(Options.TracePC || Options.TracePCGuard ||
         Options.Inline8bitCounters || Options.InlineBoolFlag);
  for (auto I : IndirCalls) {
    IRBuilder<> IRB(I);
    CallBase &CB = cast<CallBase>(*I);
    Value *Callee = CB.getCalledOperand();
    if (isa<InlineAsm>(Callee))
      continue;
    IRB.CreateCall(SanCovTracePCIndir, IRB.CreatePointerCast(Callee, IntptrTy));
  }
}

// For every switch statement we insert a call:
// __sanitizer_cov_trace_switch(CondValue,
//      {NumCases, ValueSizeInBits, Case0Value, Case1Value, Case2Value, ... })

void ModuleSanitizerCoverageCFG::InjectTraceForSwitch(
    Function &, ArrayRef<Instruction *> SwitchTraceTargets) {
  for (auto I : SwitchTraceTargets) {
    if (SwitchInst *SI = dyn_cast<SwitchInst>(I)) {
      IRBuilder<> IRB(I);
      SmallVector<Constant *, 16> Initializers;
      Value *Cond = SI->getCondition();
      if (Cond->getType()->getScalarSizeInBits() >
          Int64Ty->getScalarSizeInBits())
        continue;
      Initializers.push_back(ConstantInt::get(Int64Ty, SI->getNumCases()));
      Initializers.push_back(
          ConstantInt::get(Int64Ty, Cond->getType()->getScalarSizeInBits()));
      if (Cond->getType()->getScalarSizeInBits() <
          Int64Ty->getScalarSizeInBits())
        Cond = IRB.CreateIntCast(Cond, Int64Ty, false);
      for (auto It : SI->cases()) {
        Constant *C = It.getCaseValue();
        if (C->getType()->getScalarSizeInBits() <
            Int64Ty->getScalarSizeInBits())
          C = ConstantExpr::getCast(CastInst::ZExt, It.getCaseValue(), Int64Ty);
        Initializers.push_back(C);
      }
      llvm::sort(drop_begin(Initializers, 2),
                 [](const Constant *A, const Constant *B) {
                   return cast<ConstantInt>(A)->getLimitedValue() <
                          cast<ConstantInt>(B)->getLimitedValue();
                 });
      ArrayType *ArrayOfInt64Ty = ArrayType::get(Int64Ty, Initializers.size());
      GlobalVariable *GV = new GlobalVariable(
          *CurModule, ArrayOfInt64Ty, false, GlobalVariable::InternalLinkage,
          ConstantArray::get(ArrayOfInt64Ty, Initializers),
          "__sancov_gen_cov_switch_values");
      IRB.CreateCall(SanCovTraceSwitchFunction,
                     {Cond, IRB.CreatePointerCast(GV, Int64PtrTy)});
    }
  }
}

void ModuleSanitizerCoverageCFG::InjectTraceForDiv(
    Function &, ArrayRef<BinaryOperator *> DivTraceTargets) {
  for (auto BO : DivTraceTargets) {
    IRBuilder<> IRB(BO);
    Value *A1 = BO->getOperand(1);
    if (isa<ConstantInt>(A1)) continue;
    if (!A1->getType()->isIntegerTy())
      continue;
    uint64_t TypeSize = DL->getTypeStoreSizeInBits(A1->getType());
    int CallbackIdx = TypeSize == 32 ? 0 :
        TypeSize == 64 ? 1 : -1;
    if (CallbackIdx < 0) continue;
    auto Ty = Type::getIntNTy(*C, TypeSize);
    IRB.CreateCall(SanCovTraceDivFunction[CallbackIdx],
                   {IRB.CreateIntCast(A1, Ty, true)});
  }
}

void ModuleSanitizerCoverageCFG::InjectTraceForGep(
    Function &, ArrayRef<GetElementPtrInst *> GepTraceTargets) {
  for (auto GEP : GepTraceTargets) {
    IRBuilder<> IRB(GEP);
    for (Use &Idx : GEP->indices())
      if (!isa<ConstantInt>(Idx) && Idx->getType()->isIntegerTy())
        IRB.CreateCall(SanCovTraceGepFunction,
                       {IRB.CreateIntCast(Idx, IntptrTy, true)});
  }
}

void ModuleSanitizerCoverageCFG::InjectTraceForLoadsAndStores(
    Function &, ArrayRef<LoadInst *> Loads, ArrayRef<StoreInst *> Stores) {
  auto CallbackIdx = [&](Type *ElementTy) -> int {
    uint64_t TypeSize = DL->getTypeStoreSizeInBits(ElementTy);
    return TypeSize == 8     ? 0
           : TypeSize == 16  ? 1
           : TypeSize == 32  ? 2
           : TypeSize == 64  ? 3
           : TypeSize == 128 ? 4
                             : -1;
  };
  Type *PointerType[5] = {Int8PtrTy, Int16PtrTy, Int32PtrTy, Int64PtrTy,
                          Int128PtrTy};
  for (auto LI : Loads) {
    IRBuilder<> IRB(LI);
    auto Ptr = LI->getPointerOperand();
    int Idx = CallbackIdx(LI->getType());
    if (Idx < 0)
      continue;
    IRB.CreateCall(SanCovLoadFunction[Idx],
                   IRB.CreatePointerCast(Ptr, PointerType[Idx]));
  }
  for (auto SI : Stores) {
    IRBuilder<> IRB(SI);
    auto Ptr = SI->getPointerOperand();
    int Idx = CallbackIdx(SI->getValueOperand()->getType());
    if (Idx < 0)
      continue;
    IRB.CreateCall(SanCovStoreFunction[Idx],
                   IRB.CreatePointerCast(Ptr, PointerType[Idx]));
  }
}

void ModuleSanitizerCoverageCFG::InjectTraceForCmp(
    Function &, ArrayRef<Instruction *> CmpTraceTargets) {
  for (auto I : CmpTraceTargets) {
    if (ICmpInst *ICMP = dyn_cast<ICmpInst>(I)) {
      IRBuilder<> IRB(ICMP);
      Value *A0 = ICMP->getOperand(0);
      Value *A1 = ICMP->getOperand(1);
      if (!A0->getType()->isIntegerTy())
        continue;
      uint64_t TypeSize = DL->getTypeStoreSizeInBits(A0->getType());
      int CallbackIdx = TypeSize == 8 ? 0 :
                        TypeSize == 16 ? 1 :
                        TypeSize == 32 ? 2 :
                        TypeSize == 64 ? 3 : -1;
      if (CallbackIdx < 0) continue;
      // __sanitizer_cov_trace_cmp((type_size << 32) | predicate, A0, A1);
      auto CallbackFunc = SanCovTraceCmpFunction[CallbackIdx];
      bool FirstIsConst = isa<ConstantInt>(A0);
      bool SecondIsConst = isa<ConstantInt>(A1);
      // If both are const, then we don't need such a comparison.
      if (FirstIsConst && SecondIsConst) continue;
      // If only one is const, then make it the first callback argument.
      if (FirstIsConst || SecondIsConst) {
        CallbackFunc = SanCovTraceConstCmpFunction[CallbackIdx];
        if (SecondIsConst)
          std::swap(A0, A1);
      }

      auto Ty = Type::getIntNTy(*C, TypeSize);
      IRB.CreateCall(CallbackFunc, {IRB.CreateIntCast(A0, Ty, true),
              IRB.CreateIntCast(A1, Ty, true)});
    }
  }
}

void ModuleSanitizerCoverageCFG::InjectCoverageAtBlock(Function &F, BasicBlock &BB,
                                                    size_t Idx,
                                                    bool IsLeafFunc) {
  BasicBlock::iterator IP = BB.getFirstInsertionPt();
  bool IsEntryBB = &BB == &F.getEntryBlock();
  DebugLoc EntryLoc;
  if (IsEntryBB) {
    if (auto SP = F.getSubprogram())
      EntryLoc = DILocation::get(SP->getContext(), SP->getScopeLine(), 0, SP);
    // Keep static allocas and llvm.localescape calls in the entry block.  Even
    // if we aren't splitting the block, it's nice for allocas to be before
    // calls.
    IP = PrepareToSplitEntryBlock(BB, IP);
  } else {
    EntryLoc = IP->getDebugLoc();
    if (!EntryLoc)
      if (auto *SP = F.getSubprogram())
        EntryLoc = DILocation::get(SP->getContext(), 0, 0, SP);
  }

  IRBuilder<> IRB(&*IP);
  IRB.SetCurrentDebugLocation(EntryLoc);
  if (Options.TracePC) {
    IRB.CreateCall(SanCovTracePC)
        ->setCannotMerge(); // gets the PC using GET_CALLER_PC.
  }
  if (Options.TracePCGuard) {
    auto GuardPtr = IRB.CreateIntToPtr(
        IRB.CreateAdd(IRB.CreatePointerCast(FunctionGuardArray, IntptrTy),
                      ConstantInt::get(IntptrTy, Idx * 4)),
        Int32PtrTy);
    IRB.CreateCall(SanCovTracePCGuard, GuardPtr)->setCannotMerge();
  }
  if (Options.Inline8bitCounters) {
    auto CounterPtr = IRB.CreateGEP(
        Function8bitCounterArray->getValueType(), Function8bitCounterArray,
        {ConstantInt::get(IntptrTy, 0), ConstantInt::get(IntptrTy, Idx)});
    auto Load = IRB.CreateLoad(Int8Ty, CounterPtr);
    auto Inc = IRB.CreateAdd(Load, ConstantInt::get(Int8Ty, 1));
    auto Store = IRB.CreateStore(Inc, CounterPtr);
    SetNoSanitizeMetadata(Load);
    SetNoSanitizeMetadata(Store);
  }
  if (Options.InlineBoolFlag) {
    auto FlagPtr = IRB.CreateGEP(
        FunctionBoolArray->getValueType(), FunctionBoolArray,
        {ConstantInt::get(IntptrTy, 0), ConstantInt::get(IntptrTy, Idx)});
    auto Load = IRB.CreateLoad(Int1Ty, FlagPtr);
    auto ThenTerm =
        SplitBlockAndInsertIfThen(IRB.CreateIsNull(Load), &*IP, false);
    IRBuilder<> ThenIRB(ThenTerm);
    auto Store = ThenIRB.CreateStore(ConstantInt::getTrue(Int1Ty), FlagPtr);
    SetNoSanitizeMetadata(Load);
    SetNoSanitizeMetadata(Store);
  }
  if (Options.StackDepth && IsEntryBB && !IsLeafFunc) {
    // Check stack depth.  If it's the deepest so far, record it.
    Module *M = F.getParent();
    Function *GetFrameAddr = Intrinsic::getDeclaration(
        M, Intrinsic::frameaddress,
        IRB.getInt8PtrTy(M->getDataLayout().getAllocaAddrSpace()));
    auto FrameAddrPtr =
        IRB.CreateCall(GetFrameAddr, {Constant::getNullValue(Int32Ty)});
    auto FrameAddrInt = IRB.CreatePtrToInt(FrameAddrPtr, IntptrTy);
    auto LowestStack = IRB.CreateLoad(IntptrTy, SanCovLowestStack);
    auto IsStackLower = IRB.CreateICmpULT(FrameAddrInt, LowestStack);
    auto ThenTerm = SplitBlockAndInsertIfThen(IsStackLower, &*IP, false);
    IRBuilder<> ThenIRB(ThenTerm);
    auto Store = ThenIRB.CreateStore(FrameAddrInt, SanCovLowestStack);
    SetNoSanitizeMetadata(LowestStack);
    SetNoSanitizeMetadata(Store);
  }
}

std::string
ModuleSanitizerCoverageCFG::getSectionName(const std::string &Section) const {
  if (TargetTriple.isOSBinFormatCOFF()) {
    if (Section == SanCovCountersSectionName)
      return ".SCOV$CM";
    if (Section == SanCovBoolFlagSectionName)
      return ".SCOV$BM";
    if (Section == SanCovPCsSectionName)
      return ".SCOVP$M";
    return ".SCOV$GM"; // For SanCovGuardsSectionName.
  }
  if (TargetTriple.isOSBinFormatMachO())
    return "__DATA,__" + Section;
  return "__" + Section;
}

std::string
ModuleSanitizerCoverageCFG::getSectionStart(const std::string &Section) const {
  if (TargetTriple.isOSBinFormatMachO())
    return "\1section$start$__DATA$__" + Section;
  return "__start___" + Section;
}

std::string
ModuleSanitizerCoverageCFG::getSectionEnd(const std::string &Section) const {
  if (TargetTriple.isOSBinFormatMachO())
    return "\1section$end$__DATA$__" + Section;
  return "__stop___" + Section;
}

 char ModuleSanitizerCoverageCFGLegacyPass::ID = 0;
 INITIALIZE_PASS_BEGIN(ModuleSanitizerCoverageCFGLegacyPass, "sancov",
                       "Pass for instrumenting coverage on functions", false,
                       false)
 INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
 INITIALIZE_PASS_DEPENDENCY(PostDominatorTreeWrapperPass)
 INITIALIZE_PASS_END(ModuleSanitizerCoverageCFGLegacyPass, "sancov",
                     "Pass for instrumenting coverage on functions", false,
                     false)
// ModulePass *llvm::createModuleSanitizerCoverageCFGLegacyPassPass(
//     const SanitizerCoverageOptions &Options,
//     const std::vector<std::string> &AllowlistFiles,
//     const std::vector<std::string> &BlocklistFiles) {
//   return new ModuleSanitizerCoverageCFGLegacyPass(Options, AllowlistFiles,
//                                                BlocklistFiles);
// }