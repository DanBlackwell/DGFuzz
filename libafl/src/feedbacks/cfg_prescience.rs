//! Utilities for peeking into the possible futures for the provided control flow graph

use alloc::{borrow::ToOwned, collections::VecDeque, string::{String, ToString}, vec::Vec};
use hashbrown::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

/// A wrapper for u32 indicating the Coverage map index for a basic block / instruction
#[derive(Hash,Copy,Clone,Debug,Eq,PartialEq,Serialize,Deserialize)]
pub struct CoverageMapIdx(u32);
libafl_bolts::impl_serdeany!(CoverageMapIdx);

/// A wrapper for u64 indicating the uuid for a basic block
#[derive(Hash,Copy,Clone,Debug,Eq,PartialEq,Serialize,Deserialize)]
pub struct BasicBlockUUID(u64);
libafl_bolts::impl_serdeany!(BasicBlockUUID);

#[derive(Clone,Debug,Serialize,Deserialize)]
/// Struct storing the relevant details for a basic block in the control flow graph
pub struct ControlFlowGraphBB {
    /// Is this the first block in a function with a coverage map index?
    /// We need this for calculating the neighbours of an indirect call,
    /// where we cannot walk forwards in the graph to this point
    is_first_cov_map_block_in_function: Option<String>,
    /// unique ID for this block, not the index it has in the coverage map
    uuid: BasicBlockUUID,
    /// the index for this block in the coverage map (note that many blocks don't have this)
    coverage_map_idx: Option<CoverageMapIdx>,
    /// A Vec of the names of all functions called within this basic block
    called_funcs: Vec<String>,
    /// The number of indirect function calls in this block
    num_indirect_calls: u32,
    /// A Vec of the `uuid`s for each basic block that is a successor of `self`
    successor_uuids: HashSet<BasicBlockUUID>,
    /// A Vec of the `CoverageMapIdx` that are successors of self
    successor_cov_map_idxs: Option<HashSet<CoverageMapIdx>>,
    /// A Vec of the coverage map indexes for all instrumented instructions in this basic block.
    /// This includes cmov's and the vector equivalent
    instrumented_instructions_cov_map_idxs: HashSet<CoverageMapIdx>,
    /// A Vec of the coverage map indexes for all neighbours of (ie blocks reachable from) this
    /// basic block. Only populated lazily when required - `None` to begin with.
    neighbours_map_idxs: Option<HashSet<CoverageMapIdx>>,
    /// The name of the function that this block is in
    function: String,
    /// Is this a dummy block (in place of missing blocks)
    dummy: bool,
}

libafl_bolts::impl_serdeany!(ControlFlowGraphBB);

#[derive(Debug,Serialize,Deserialize)]
/// Struct storing the control flow graph details
pub struct ControlFlowGraph {
    /// A vec of all the edges
    all_edges: Vec<ControlFlowGraphBB>,
    /// returns a list of indexes (for self.all_edges) which are in the func with the given name
    edges_in_func_named: HashMap<String, Vec<Vec<usize>>>,
    /// returns an index for self.all_edges with the matching uuid
    edge_with_uuid: HashMap<BasicBlockUUID, usize>,
    /// returns an index for self.all_edges with the matching coverage map index
    edge_with_coverage_map_idx: HashMap<CoverageMapIdx, usize>,
    /// A HashSet of all the IDs from functions that appear more than once
    duplicate_cov_map_idxs: HashSet<CoverageMapIdx>,
    /// List of functions that need their entry blocks recalculating (now we figured out which
    /// definition is used)
    functions_needing_recalc: HashSet<String>,
    /// List of functions that either only have one definition, or we have seen in the coverage
    confirmed_functions: HashSet<String>
}

libafl_bolts::impl_serdeany!(ControlFlowGraph);

impl ControlFlowGraph {
    /// Create a new blank `ControlFlowGraph`
    pub fn new() -> Self {
        Self { 
            all_edges: vec![],
            edges_in_func_named: HashMap::new(),
            edge_with_uuid: HashMap::new(),
            edge_with_coverage_map_idx: HashMap::new(),
            duplicate_cov_map_idxs: HashSet::new(),
            functions_needing_recalc: HashSet::new(),
            confirmed_functions: HashSet::new(),
        }
    }
    
    /// Output a GraphViz dot file
    pub fn to_graphviz_dot(&mut self) -> (String, String) {
        let mut bb_string = "digraph {\n".to_string();
        let mut functions_string = "digraph {\n".to_string();
        let mut id_for_func = HashMap::new();
        let mut external_edges_string = "".to_string();

        let mut function_id = 0;
        for (function, edge_lists) in self.edges_in_func_named.clone() {
            let func_id = if let Some(id) = id_for_func.get(&function) {
                *id
            } else {
                let len = id_for_func.len();
                id_for_func.insert(function.to_string(), len);
                len
            };
            functions_string.push_str(&format!("  {} [label = \"{}\"];\n", func_id, function));
            let edges = &edge_lists[0];
            let mut nodes_string = "".to_string();
            let mut internal_edges_string = "".to_string();
            for (pos, edge) in edges.iter().enumerate() {
                let bb = self.all_edges[*edge].clone();
                let neighbours;
                if let Some(f) = &bb.is_first_cov_map_block_in_function {
                    assert!(pos == 0 && *f == *function);
                    bb_string.push_str(&format!("  subgraph cluster_{function_id} {{\n"));
                    bb_string.push_str(        &"    style=filled;\n    color=lightgrey;\n");
                    bb_string.push_str(&format!("    label=\"{}\";\n", function));
                    let label = if let Some(idx) = bb.coverage_map_idx {
                        format!("{} ({})", idx.0, bb.uuid.0)
                    } else {
                        format!("({})", bb.uuid.0)
                    };
                    nodes_string.push_str(&format!( "    {} [label=\"{}\"];\n", bb.uuid.0, label));
                    if let Some(idx) = bb.coverage_map_idx {
                        neighbours = self.neighbours_for_coverage_map_idx(idx).iter().cloned().collect::<Vec<CoverageMapIdx>>();
                    } else if let Some(n) = self.neighbours_for_start_of_function(&function) {
                        neighbours = n.iter().cloned().collect::<Vec<CoverageMapIdx>>();
                    } else {
                        continue;
                    }
                } else if let Some(idx) = bb.coverage_map_idx {
                    nodes_string.push_str(&format!( "    {} [label=\"{}\"];\n", bb.uuid.0, idx.0));
                    neighbours = self.neighbours_for_coverage_map_idx(idx).iter().cloned().collect::<Vec<CoverageMapIdx>>();
                } else {
                    // We don't need to add this one
                    continue;
                }

                for neighbour in neighbours {
                    let mut cross_function = false;
                    let dest_node;
                    if neighbour.0 as usize >= self.all_edges.len() {
                        nodes_string.push_str(&format!("    {} [label=\"indirect_call\"];\n", neighbour.0));
                        cross_function = true;
                        dest_node = neighbour.0 as u64;
                    } else {
                        let dest_bb = &self.all_edges[neighbour.0 as usize];
                        if dest_bb.function != *function { 
                            let dest_func_id = if let Some(id) = id_for_func.get(&dest_bb.function) {
                                *id
                            } else {
                                let len = id_for_func.len();
                                id_for_func.insert(dest_bb.function.clone(), len);
                                len
                            };
                            functions_string.push_str(&format!("  {} -> {};\n", func_id, dest_func_id));
                            cross_function = true; 
                            let dest_func_edge_lists = &self.edges_in_func_named[&dest_bb.function];
                            if !edge_lists.is_empty() && !edge_lists[0].is_empty() {
                                dest_node = self.all_edges[dest_func_edge_lists[0][0]].uuid.0;
                            } else {
                                dest_node = dest_bb.uuid.0;
                            }
                        } else {
                            dest_node = dest_bb.uuid.0;
                        }
                    }
                    if cross_function { 
                        external_edges_string.push_str(&format!("  {} -> {} [style=dashed];\n", bb.uuid.0, dest_node));
                    } else { 
                        internal_edges_string.push_str(&format!("    {} -> {};\n", bb.uuid.0, dest_node));
                    };
                }
            }

            bb_string.push_str(&nodes_string);
            bb_string.push_str(&internal_edges_string);
            bb_string.push_str(&"  }\n");
            bb_string.push_str(&"\n");
            function_id += 1;
        }

        // dot_string.push_str(&external_edges_string);
        bb_string.push_str("}\n");
        functions_string.push_str(&"}\n");
        (bb_string, functions_string)
    }

    /// Is this CFG populated?
    pub fn is_empty(&self) -> bool {
        self.all_edges.is_empty()
    }

    /// Populate the control flow graph from the raw buffer (ie deserialise it)
    pub fn parse_from_buf(&mut self, buf: &[u8]) {
        let mut highest_cov_map_idx = 0;
        let mut pos = 0;

        macro_rules! parse_u32_from_be_bytes {
            ($var:ident) => {
                let $var = u32::from_be_bytes(buf[pos..pos+4].try_into().unwrap());
                // println!("parsed int {} from {pos} to {}", $var, pos + 4);
                pos += 4;
            };
        }
        macro_rules! parse_ptr_from_bytes {
            ($var:ident) => {
                let $var = u64::from_ne_bytes(buf[pos..pos+8].try_into().unwrap());
                // println!("parsed int {} from {pos} to {}", $var, pos + 8);
                pos += 8;
            };
        }

        parse_u32_from_be_bytes!(expected_indexes);

        parse_u32_from_be_bytes!(num_funcs);
        println!("from buf: {:?}, Expected {expected_indexes} indexes, and {num_funcs} funcs", &buf[0..8]);

        for _ in 0..num_funcs {
            parse_u32_from_be_bytes!(fname_len);
            let fname = String::from_utf8(buf[pos..pos+fname_len as usize].try_into().unwrap()).unwrap();
            pos += fname_len as usize;
            print!("Function (name len: {fname_len} named: {fname}");

            let mut edges_in_func = vec![];

            parse_u32_from_be_bytes!(num_bbs);
            println!(", {num_bbs} basic blocks.");
            for bb_index in 0..num_bbs {
                parse_ptr_from_bytes!(uuid);
                parse_u32_from_be_bytes!(coverage_map_idx);
                parse_u32_from_be_bytes!(num_indirect_calls);
                println!("  Next basicblock (uuid: {uuid:x}, cov_map_idx: {coverage_map_idx}): {{\n    indirect_calls: {num_indirect_calls},");

                let mut called_funcs = vec![];
                parse_u32_from_be_bytes!(num_called_funcs);
                if num_called_funcs > 0 {
                    print!("    bb {coverage_map_idx} has {num_called_funcs} called funcs:");
                    for _ in 0..num_called_funcs {
                        parse_u32_from_be_bytes!(fname_len);
                        let fname = String::from_utf8(buf[pos..pos+fname_len as usize].try_into().unwrap()).unwrap();
                        print!(" {fname}");
                        pos += fname_len as usize;
                        called_funcs.push(fname);
                    }
                    println!("");
                }

                let mut successor_uuids = HashSet::new();
                parse_u32_from_be_bytes!(num_successors);
                if num_successors > 0 {
                    print!("    successors: ");
                    for _ in 0..num_successors {
                        parse_ptr_from_bytes!(successor_uuid);
                        print!(" {successor_uuid:x}");
                        successor_uuids.insert(BasicBlockUUID(successor_uuid));
                    }
                    println!("");
                }

                let mut instrumented_instructions_cov_map_idxs = HashSet::new();
                parse_u32_from_be_bytes!(num_instrs);
                if num_instrs > 0 {
                    print!("    instrumented_instrs:");
                    for _ in 0..num_instrs {
                        parse_u32_from_be_bytes!(instr_idx);
                        print!(" {instr_idx}");
                        instrumented_instructions_cov_map_idxs.insert(CoverageMapIdx(instr_idx));
                    }
                    println!("");
                }
                println!("  }}");

                let bb = ControlFlowGraphBB {
                    is_first_cov_map_block_in_function: if bb_index == 0 { 
                        Some(fname.clone()) 
                    } else { 
                        None 
                    },
                    uuid: BasicBlockUUID(uuid), 
                    coverage_map_idx: if coverage_map_idx != u32::MAX { 
                        Some(CoverageMapIdx(coverage_map_idx)) 
                    } else { 
                        None 
                    },
                    called_funcs,
                    num_indirect_calls,
                    successor_uuids,
                    successor_cov_map_idxs: None,
                    instrumented_instructions_cov_map_idxs,
                    neighbours_map_idxs: None,
                    function: fname.clone(),
                    dummy: false,
                };
                let index = self.all_edges.len();

                self.edge_with_uuid.insert(bb.uuid, index);
                if let Some(idx) = bb.coverage_map_idx {
                    self.edge_with_coverage_map_idx.insert(idx, index);
                    if idx.0 > highest_cov_map_idx {
                        highest_cov_map_idx = idx.0;
                    }
                } 
                for &instr_idx in &bb.instrumented_instructions_cov_map_idxs {
                    self.edge_with_coverage_map_idx.insert(instr_idx, index);
                }
                edges_in_func.push(index);
                self.all_edges.push(bb);
            }

            if !edges_in_func.is_empty() {
                // Ok, without an LTO pass we sometimes have multiple definitions of the same function
                // - only one should be used, but we don't know which yet...
                if let Some(edge_lists) = self.edges_in_func_named.get_mut(&fname) {
                    println!("Found {} sets of definitions for func {fname}, with {:?} BBs and the latest with {} BBs",
                             edge_lists.len() + 1, 
                             edge_lists.iter().map(|x| x.len()).collect::<Vec<usize>>(), 
                             edges_in_func.len());
                    edge_lists.push(edges_in_func);
                } else {
                    self.edges_in_func_named.insert(fname.clone(), vec![edges_in_func]);
                }
                println!("Edges in func {fname}: {:?}", self.edges_in_func_named[&fname]);
            }

            println!("Reached {pos} from a total len: {}", buf.len());
        }

        if self.all_edges.len() != expected_indexes as usize {
            println!("expected: {expected_indexes} edges, but got {}", self.all_edges.len());
        }

        // Here we rewrite the all_edges vec so that the coverage map index aligns with the vec
        // index. This allows us to skip a layer of indirection and do fast graph traversal. This
        // code is finnicky, don't mess with it... (but the assertions should help if you do)
        let mut aligned_bbs = vec![];
        let mut replacement_edges_in_func_named = HashMap::new();
        let mut unstored_uuids = self.all_edges.iter()
            .map(|bb| bb.uuid)
            .collect::<HashSet<BasicBlockUUID>>();

        println!("Populating aligned_bbs 0..={highest_cov_map_idx}");
        for idx in 0..=highest_cov_map_idx {
            assert!(aligned_bbs.len() == idx as usize);

            if let Some(all_edges_idx) = self.edge_with_coverage_map_idx.get(&CoverageMapIdx(idx)) {
                let bb = self.all_edges[*all_edges_idx].clone(); 
                unstored_uuids.remove(&bb.uuid);
                self.edge_with_uuid.insert(bb.uuid, idx as usize);

                // There may be multiple definitions of this function, find out which one this is
                let edge_lists = self.edges_in_func_named.get_mut(&bb.function).unwrap();
                if edge_lists.len() == 1 { self.confirmed_functions.insert(bb.function.clone()); }
                let mut version = 99999;
                for (idx, edge_list) in edge_lists.iter().enumerate() {
                    if edge_list.contains(all_edges_idx) {
                        version = idx;
                        break;
                    }
                }
                if version == 99999 { 
                    panic!("couldn't find edge {all_edges_idx} (cov_idx: {idx}) in edge_lists for {} ({:?})", bb.function, edge_lists); 
                }

                let new_edge_lists = {
                    if let Some(res) = replacement_edges_in_func_named.get_mut(&bb.function) {
                        res
                    } else {
                        replacement_edges_in_func_named.insert(bb.function.clone(), vec![]);
                        replacement_edges_in_func_named.get_mut(&bb.function).unwrap()
                    }
                };
                while new_edge_lists.len() <= version {
                    new_edge_lists.push(vec![]);
                }

                if bb.is_first_cov_map_block_in_function.is_some() {
                    new_edge_lists[version].insert(0, idx as usize);
                } else {
                    new_edge_lists[version].push(idx as usize);
                }

                aligned_bbs.push(bb);

            } else {
                println!("Inserting bogus block at {idx}");
                aligned_bbs.push(ControlFlowGraphBB {
                    is_first_cov_map_block_in_function: None,
                    uuid: BasicBlockUUID(0), 
                    coverage_map_idx: None,
                    called_funcs: vec![],
                    num_indirect_calls: 0,
                    successor_uuids: HashSet::new(),
                    successor_cov_map_idxs: None,
                    instrumented_instructions_cov_map_idxs: HashSet::new(),
                    neighbours_map_idxs: None,
                    function: "HELP I SCREWED UP!".to_string(),
                    dummy: true,
                });
            }
        }

        assert!(aligned_bbs.len() == (highest_cov_map_idx + 1) as usize, "have {} aligned_bbs only! {:?}", aligned_bbs.len(),
            aligned_bbs.iter().map(|bb| bb.coverage_map_idx).collect::<Vec<Option<CoverageMapIdx>>>());

        for unstored_uuid in unstored_uuids {
            let all_edges_idx = self.edge_with_uuid[&unstored_uuid];
            let bb = self.all_edges[all_edges_idx].clone();
            assert!(bb.uuid == unstored_uuid && bb.coverage_map_idx.is_none(),
                    "bb.uuid: {:?} should = {:?} and bb.coverage_map_idx should be none (is {:?})",
                    bb.uuid, unstored_uuid, bb.coverage_map_idx);
            let new_index = aligned_bbs.len();
            self.edge_with_uuid.insert(unstored_uuid, new_index);

            // There may be multiple definitions of this function, find out which one this is
            let edge_lists = self.edges_in_func_named.get_mut(&bb.function).unwrap();
            if edge_lists.len() == 1 { self.confirmed_functions.insert(bb.function.clone()); }
            let mut version = 99999;
            for (idx, edge_list) in edge_lists.iter().enumerate() {
                if edge_list.contains(&all_edges_idx) {
                    version = idx;
                    break;
                }
            }
            if version == 99999 { panic!("couldn't find edge {all_edges_idx} in edge_lists for {}", bb.function); }

            let new_edge_lists = {
                if let Some(res) = replacement_edges_in_func_named.get_mut(&bb.function) {
                    res
                } else {
                    replacement_edges_in_func_named.insert(bb.function.clone(), vec![]);
                    replacement_edges_in_func_named.get_mut(&bb.function).unwrap()
                }
            };
            while new_edge_lists.len() <= version {
                new_edge_lists.push(vec![]);
            }

            if bb.is_first_cov_map_block_in_function.is_some() {
                new_edge_lists[version].insert(0, new_index);
            } else {
                new_edge_lists[version].push(new_index);
            }

            aligned_bbs.push(bb);
        }

//        assert!(stored_first_uuid_for_func == evicted_funcs, "stored firsts for: {:?}, but missed out: {:?}", stored_first_uuid_for_func, evicted_funcs.difference(&stored_first_uuid_for_func));

        // Make sure that the most reachable version of the function is used for early calcs...
        for (_func, edge_lists) in &mut replacement_edges_in_func_named {
            let mut highest_reachability = 0;
            let mut best_index = 0;
            for (index, edge_list) in edge_lists.iter().enumerate() {
                let mut reachability = 0;
                for edge in edge_list {
                    let bb = &self.all_edges[*edge];
                    if bb.coverage_map_idx.is_some() { reachability += 1; }
                    reachability += bb.called_funcs.len();
                    reachability += bb.num_indirect_calls as usize;
                }
                if reachability > highest_reachability {
                    highest_reachability = reachability;
                    best_index = index;
                }
            }
            if best_index != 0 {
                edge_lists.swap(0, best_index);
            }
        }
        self.edges_in_func_named = replacement_edges_in_func_named;
        self.all_edges = aligned_bbs;
        println!("all_edges len now: {}", self.all_edges.len());

        let funcs = self.edges_in_func_named.keys().cloned().collect::<Vec<String>>();
        for func in funcs {
            self.neighbours_for_start_of_function(&func);
        }
    }

    /// return a Vec of the coverage map indexes that can be directly reached from a function call
    fn neighbours_for_start_of_function(&mut self, function_name: &String) -> Option<HashSet<CoverageMapIdx>> {
        let edge_lists = self.edges_in_func_named.get(function_name);
        // this function is not instrumented
        if edge_lists.is_none() { return None; }

        let mut edges_in_func = None;
        for edge_list in edge_lists.unwrap() {
            if !edge_list.is_empty() {
                edges_in_func = Some(edge_list);
                break;
            }
        }

        // Seems there's no instrumentation...
        if edges_in_func.is_none() { return None; }
        
        let first_idx = edges_in_func.unwrap()[0];
        let first_bb = &self.all_edges[first_idx];

        if let Some(idx) = first_bb.coverage_map_idx {
            let mut res = HashSet::new();
            res.insert(idx);
            return Some(res);
        }

        if first_bb.neighbours_map_idxs.is_none() {
            let cur_uuid = first_bb.uuid.clone();
            let mut neighbours = first_bb.instrumented_instructions_cov_map_idxs.to_owned();
            // this block is not instrumented, so find the first successors that are
            let successors = first_bb.successor_uuids.clone();
            for succ_uuid in successors {
                let mut predecessors = HashSet::new();
                predecessors.insert(cur_uuid);
                self.append_first_cov_map_idxs(&mut neighbours, &mut predecessors, succ_uuid);
            }

            for &neighbour in &neighbours {
                let bb = &mut self.all_edges[neighbour.0 as usize];
                // we need to set the neighbours for this BB to be all the other ones
                // in case this is the target of an indirect call
                if bb.function == *function_name && bb.neighbours_map_idxs.is_none() {
                    let mut all_neighbours = neighbours.clone();
                    all_neighbours.remove(&neighbour);
                    for succ in self.neighbours_for_coverage_map_idx(neighbour) {
                        all_neighbours.insert(*succ);
                    }
                    self.all_edges[neighbour.0 as usize].neighbours_map_idxs = Some(all_neighbours);
                }
                // self.all_edges[neighbour.0 as usize].is_first_cov_map_block_in_function = Some(function_name.to_owned());
            }

            self.all_edges[first_idx].neighbours_map_idxs = Some(neighbours);
        }

        Some(self.all_edges[first_idx].neighbours_map_idxs.as_ref().unwrap().to_owned())
    }

    /// return a Vec of the coverage map indexes that can be directly reached from `coverage_idx`
    fn neighbours_for_coverage_map_idx(&mut self, coverage_idx: CoverageMapIdx) -> &HashSet<CoverageMapIdx> {
        let bb = &self.all_edges[coverage_idx.0 as usize];
        if bb.neighbours_map_idxs.is_none() {
            let mut neighbours = bb.instrumented_instructions_cov_map_idxs.to_owned();

            for indirect_call_num in 0..bb.num_indirect_calls {
                // create a unique ID for this indirect call based on the coverage map index
                let idx = 1_000_000 + (bb.uuid.0 as usize & 0xFFFFFFFF) + indirect_call_num as usize;
                neighbours.insert(CoverageMapIdx(idx as u32));
            }

            let cur_uuid = bb.uuid.clone();
            let called_funcs = bb.called_funcs.clone();
            let succ_uuids = bb.successor_uuids.clone();
            for func in called_funcs {
                println!("Exploring func: {func}");
                if let Some(func_neighbours) = self.neighbours_for_start_of_function(&func) {
                    println!("{func} neighbours: {:?}", func_neighbours);
                    for neighbour in func_neighbours {
                        neighbours.insert(neighbour);
                    }
                }
            }

            for succ_uuid in succ_uuids {
                let mut predecessors = HashSet::new();
                predecessors.insert(cur_uuid);
                self.append_first_cov_map_idxs(&mut neighbours, &mut predecessors, succ_uuid);
            }

            self.all_edges[coverage_idx.0 as usize].neighbours_map_idxs = Some(neighbours.clone());
        }

        self.all_edges[coverage_idx.0 as usize].neighbours_map_idxs.as_ref().unwrap()
    }

    /// Return a &HashSet that gives us all the coverageMapIdxs that are successors of the given
    /// `coverage_idx`
    fn successor_cov_map_idxs_for(&mut self, coverage_idx: CoverageMapIdx) -> &HashSet<CoverageMapIdx> {
        let bb = &self.all_edges[coverage_idx.0 as usize];
        let cur_uuid = bb.uuid.clone();
        if bb.successor_cov_map_idxs.is_none() {
            let mut neighbours = HashSet::new();
            for succ_uuid in bb.successor_uuids.clone() {
                let mut predecessors = HashSet::new();
                predecessors.insert(cur_uuid);
                self.append_first_cov_map_idxs(&mut neighbours, &mut predecessors, succ_uuid);
            }

            self.all_edges[coverage_idx.0 as usize].successor_cov_map_idxs = Some(neighbours.clone());
        }

        self.all_edges[coverage_idx.0 as usize].successor_cov_map_idxs.as_ref().unwrap()
    }

    /// Return a Vec of the first coverage map indexes that can be reached from the block with a given uuid
    fn append_first_cov_map_idxs(&mut self, covered: &mut HashSet<CoverageMapIdx>, predecessors: &mut HashSet<BasicBlockUUID>, uuid: BasicBlockUUID) {
        let idx = self.edge_with_uuid.get(&uuid).unwrap();
        let bb = &mut self.all_edges[*idx];

        if let Some(this_idx) = bb.coverage_map_idx {
            covered.insert(this_idx);
        } else {
            for &instr in &bb.instrumented_instructions_cov_map_idxs {
                covered.insert(instr);
            }

            for indirect_call_num in 0..bb.num_indirect_calls {
                // create a unique ID for this indirect call based on the coverage map index
                let idx = 1_000_000 + (bb.uuid.0 as usize & 0xFFFFFFFF) + indirect_call_num as usize;
                covered.insert(CoverageMapIdx(idx as u32));
            }

            let funcs = bb.called_funcs.clone();
            for succ_uuid in bb.successor_uuids.clone() { 
                if predecessors.insert(succ_uuid) {
                    self.append_first_cov_map_idxs(covered, predecessors, succ_uuid);
                }
            }

            for func in funcs {
                if let Some(neighbours) = self.neighbours_for_start_of_function(&func) {
                    for cov_idx in neighbours {
                        covered.insert(cov_idx);
                    }
                }
            }
        }
    }

    /// Go through all these indexes and see if there are any from functions with multiple definitions
    pub fn check_for_functions_needing_recalc(&mut self, input_coverage_map_indexes: &[usize]) {
        let mut covered_funcs = HashSet::new();
        let mut index_for_func = HashMap::new();
        for idx in input_coverage_map_indexes {
            let func = &self.all_edges[*idx].function;
            if covered_funcs.insert(func) {
                index_for_func.insert(func, *idx);
            }
        }

        let mut need_full_recalc = false;
        let mut funcs_needing_recalc = HashSet::new();
        for func in covered_funcs {
            if !self.confirmed_functions.contains(func) {
                let edge_lists = self.edges_in_func_named.get(func).unwrap();
                let sought_index = index_for_func.get(func).unwrap();
                let mut list_num = 99999;
                for (idx, edge_list) in edge_lists.iter().enumerate() {
                    if edge_list.contains(sought_index) {
                        list_num = idx;
                        break;
                    }
                }
                if list_num == 99999 {
                    panic!("Couldn't find {sought_index} in edge_lists for {func}");
                }

                if list_num != 0 {
                    let edge_lists = self.edges_in_func_named.get_mut(func).unwrap();
                    // Swap this into 0
                    edge_lists.swap(list_num, 0);
                    need_full_recalc = true;
                    funcs_needing_recalc.insert(func.clone());
                    println!("Had to swap {list_num} with 0 for function with multiple definitions ({func}). Should now recalc");
                }

                // Ok, we know which version of this function is used now for sure
                self.confirmed_functions.insert(func.to_owned());
            }
        }

        drop(index_for_func);

        if need_full_recalc {
            for bb in &mut self.all_edges {
                // Set this as None again to force recalc
                bb.neighbours_map_idxs = None;
                bb.successor_cov_map_idxs = None;
            }
        }

        for func in funcs_needing_recalc {
            self.neighbours_for_start_of_function(&func);
        }
    }

    /// Return a set of all neighbours directly reachable from the list of `coverage_map_indexes`.
    pub fn get_all_direct_neighbours(&mut self, coverage_map_indexes: &[usize]) -> HashSet<usize> {
        let original_indexes: HashSet<usize> = HashSet::from_iter(coverage_map_indexes.iter().copied());
        let mut set = HashSet::new();
        for &cov_idx in coverage_map_indexes {
            // the instrumentation skips these values so...
            if cov_idx < 4 { continue; }
            let neighbours = self.neighbours_for_coverage_map_idx(CoverageMapIdx(cov_idx as u32));
            for &neighbour in neighbours { 
                // filter out the edges we were given
                if !original_indexes.contains(&(neighbour.0 as usize)) {
                    set.insert(neighbour.0 as usize); 
                }
            }
        }

        set
    }


    /// Return a set of all indexes reachable from the list of `coverage_map_indexes` and the set
    /// of called functions
    pub fn get_all_neighbours_full_depth(
        &mut self, 
        input_coverage_map_indexes: &[usize],
        all_coverage_map_indexes: &HashSet<usize>
    ) -> (HashSet<(usize, usize)>, HashSet<String>) {
        self.get_all_neighbours_upto_depth(input_coverage_map_indexes, all_coverage_map_indexes, 99999)
    }

    /// Return a set of all indexes reachable from the list of `coverage_map_indexes` and the set
    /// of called functions
    pub fn get_all_neighbours_upto_depth(
        &mut self, 
        input_coverage_map_indexes: &[usize],
        all_coverage_map_indexes: &HashSet<usize>,
        max_depth: usize,
    ) -> (HashSet<(usize, usize)>, HashSet<String>) {
        let mut dupes = vec![];
        for idx in input_coverage_map_indexes {
            if self.duplicate_cov_map_idxs.contains(&CoverageMapIdx(*idx as u32)) {
                dupes.push(*idx);
            }
        }
        if dupes.len() > 0 {
            println!("Found duplicate coverage map indexes: {:?}", dupes);
        }

        // set any indexes we've already covered...
        let mut covered = all_coverage_map_indexes.clone();
        let mut reachable = HashSet::new();
        let mut queue = VecDeque::new();
        for &idx in input_coverage_map_indexes {
            queue.push_back((1, idx));
        }
        let mut hit_functions = HashSet::new();

//        assert!(input_coverage_map_indexes.clone().into_iter().copied().collect::<HashSet<usize>>().is_subset(all_coverage_map_indexes));

        while let Some((depth, to_explore)) = queue.pop_front() {

            debug_assert!(covered.contains(&to_explore), "to_explore: {to_explore}, covered: {:?}", covered);

            if to_explore >= 1_000_000 {
                // can't follow an indirect call...
                continue;
            }

            if depth > max_depth {
                continue;
            }

            {
                let bb = &self.all_edges[to_explore];

                if let Some(func) = &bb.is_first_cov_map_block_in_function {
                    let func = func.to_owned();
                    hit_functions.insert(func.clone());
                    if let Some(neighbours) = self.neighbours_for_start_of_function(&func) {
                        for neighbour in neighbours {
                            if covered.insert(neighbour.0 as usize) {
                                reachable.insert((depth, neighbour.0 as usize));
                                queue.push_back((depth + 1, neighbour.0 as usize));
                            }
                        }
                    }
                }
            }


            {
                let bb = &self.all_edges[to_explore];

                // Can't make this assertion as we may have a basic block which contains only
                // instrumented instructions
                for func in bb.called_funcs.clone() {
                    if hit_functions.insert(func.clone()) {
                       if let Some(neighbours) = self.neighbours_for_start_of_function(&func) {
                           for neighbour in neighbours {
                               if covered.insert(neighbour.0 as usize) {
                                    reachable.insert((depth, neighbour.0 as usize));
                                    queue.push_back((depth + 1, neighbour.0 as usize));
                               }
                           }
                       }
                    }
                }
            }

            let bb = &self.all_edges[to_explore];

            for instr_cov_map_idx in bb.instrumented_instructions_cov_map_idxs.clone() {
                if covered.insert(instr_cov_map_idx.0 as usize) {
                    reachable.insert((depth, instr_cov_map_idx.0 as usize));
                }
            }

            for indirect_call_num in 0..bb.num_indirect_calls {
                // create a unique ID for this indirect call based on the coverage map index
                let idx = 1_000_000 + (bb.uuid.0 as usize & 0xFFFFFFFF) + indirect_call_num as usize;
                if covered.insert(idx) {
                    reachable.insert((depth, idx));
                }
            }

            for successor in self.successor_cov_map_idxs_for(CoverageMapIdx(to_explore as u32)).to_owned() {
                let map_idx = successor.0 as usize;
                if covered.insert(map_idx) {
                    reachable.insert((depth, map_idx));
                    queue.push_back((depth + 1, map_idx));
                }
            }
        }

        (reachable, hit_functions)
    }

    /// Get a list of the functions hit by a list of coverage map indexes
    pub fn functions_hit_by_cov_map_idxs(&self, coverage_map_indexes: &[usize]) -> HashSet<String> {
        let mut called = HashSet::new();

        for &cov_idx in coverage_map_indexes {
            if cov_idx < 4 { continue; }
            let bb = &self.all_edges[cov_idx];
            called.insert(bb.function.clone());
        }

        called
    }

    /// Return a map from parent edges to a list of their direct neighbours (descendents)
    pub fn get_map_from_edges_to_direct_neighbours(
        &mut self, 
        input_coverage_map_indexes: &[usize],
        all_coverage_map_indexes: &HashSet<usize>,
    ) -> HashMap<usize, Vec<usize>> {

        let mut neighbours_info = HashMap::new();

        for &to_explore in input_coverage_map_indexes {
            if to_explore >= 1_000_000 {
                // can't follow an indirect call...
                continue;
            }

            // set any indexes we've already covered...
            let mut covered = all_coverage_map_indexes.clone();

            let mut children = vec![];

            {
                let bb = &self.all_edges[to_explore];

                if let Some(func) = &bb.is_first_cov_map_block_in_function {
                    let func = func.to_owned();
                    if let Some(neighbours) = self.neighbours_for_start_of_function(&func) {
                        for neighbour in neighbours {
                            if covered.insert(neighbour.0 as usize) {
                                children.push(neighbour.0 as usize)
                            }
                        }
                    }
                }
            }

            {
                let bb = &self.all_edges[to_explore];

                // Can't make this assertion as we may have a basic block which contains only
                // instrumented instructions
                for func in bb.called_funcs.clone() {
                    if let Some(neighbours) = self.neighbours_for_start_of_function(&func) {
                        for neighbour in neighbours {
                            if covered.insert(neighbour.0 as usize) {
                                children.push(neighbour.0 as usize)
                            }
                        }
                    }
                }
            }

            let bb = &self.all_edges[to_explore];

            for instr_cov_map_idx in bb.instrumented_instructions_cov_map_idxs.clone() {
                if covered.insert(instr_cov_map_idx.0 as usize) {
                    children.push(instr_cov_map_idx.0 as usize);
                }
            }

            // DO NOT add these huge index indirect calls
            // for indirect_call_num in 0..bb.num_indirect_calls {

            for successor in self.successor_cov_map_idxs_for(CoverageMapIdx(to_explore as u32)).to_owned() {
                let map_idx = successor.0 as usize;
                if covered.insert(map_idx) {
                    children.push(map_idx);
                }
            }

            if !children.is_empty() {
                neighbours_info.insert(to_explore, children);
            }
        }

        neighbours_info
    }
}
