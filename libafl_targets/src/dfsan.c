#include "dfsan.h"
#include <sanitizer/dfsan_interface.h>
#include <stdio.h>
#include <string.h>

extern int LLVMFuzzerTestOneInput(uint8_t *Data, size_t Size);
void dfsan_found_conditional(dfsan_label label, dfsan_origin origin);

void __dfsan_init() {
    printf("Setting dfsan callback to %p\n", dfsan_found_conditional);
    dfsan_set_conditional_callback(dfsan_found_conditional);
}

void __tag_input_with_labels(
    unsigned char *input, 
    size_t input_len,
    size_t *label_start_offsets, 
    size_t *label_block_len, 
    int num_labels
) {
    memset(dfsan_labels_following_edge, 0, sizeof(dfsan_labels_following_edge));
    dfsan_flush();
    dfsan_label labels[8] = {1, 2, 4, 8, 16, 32, 64, 128};
    for (int i = 0; i < num_labels; i++) {
        dfsan_set_label(labels[i], input + label_start_offsets[i], label_block_len[i]);
        // printf("Setting label %hhu [%lu..%lu)\n", labels[i], label_start_offsets[i], label_start_offsets[i] + label_block_len[i]);
    }

    printf("will call LLVMFuzzer... at %p\n", LLVMFuzzerTestOneInput);
    LLVMFuzzerTestOneInput(input, input_len);
    // do not reset labels as below; this breaks the callback somehow
    // dfsan_set_label(0, input, input_len);
}

void dfsan_found_conditional(dfsan_label label, dfsan_origin origin) {
    printf("hit DFSAN callback (last edge: %lu), have label %hu\n", LAST_SEEN_EDGE, label);
    dfsan_labels_following_edge[LAST_SEEN_EDGE] = label;
}