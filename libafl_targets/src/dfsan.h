#ifndef DFSAN_H
#define DFSAN_H

#include <stddef.h>

unsigned char dfsan_labels_following_edge[1024 * 1024] = {0};

void __dfsan_init(void);

void __tag_input_with_labels(
    const char *input, 
    size_t *label_start_offsets, 
    size_t *label_block_len, 
    int num_labels
);

#endif