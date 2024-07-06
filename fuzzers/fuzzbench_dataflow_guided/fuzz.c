#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

int add(int a, int b) {
	return a + b;
}

int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  // fprintf(stderr, "got into LLVMFuzzerTestOneInput (DFSAN) len %lu: [", Size);
  // if (Size < 100) {
  //   for (int i = 0; i < Size; i++) fprintf(stderr, "%hhu, ", Data[i]);
  // }
  // fprintf(stderr, "\b\b]\n");

  if (Size >= 8 && *(uint32_t *)Data == 0xaabbccdd) { abort(); }
  char buf[8] = {'a', 'b', 'c', 'd'};

  if (memcmp(Data, buf, 4) == 0) { abort(); }
  add(buf[0], buf[1]);
  return 0;
}

/*
int main() {

  char buf [10] = {0};
  LLVMFuzzerTestOneInput(buf, 10);

}*/
