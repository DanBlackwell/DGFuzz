#include "dfsan.h"
#include <sanitizer/dfsan_interface.h>

unsigned int last_edge = 0;

void __dfsan_init() {
    dfsan_set_conditional_callback(dfsan_found_conditional);
}

void __tag_input_with_labels(
    const char *input, 
    size_t *label_start_offsets, 
    size_t *label_block_len, 
    int num_labels
) {
    dfsan_flush();
    dfsan_label labels[8] = {1, 2, 4, 8, 16, 32, 64, 128};
    for (int i = 0; i < num_labels; i++) {
        dfsan_set_label(labels[i], input + label_start_offsets[i], label_block_len[i]);
    }
}

void dfsan_found_conditional(dfsan_label label, dfsan_origin origin) {
    dfsan_labels_following_edge[last_edge] = label;
}