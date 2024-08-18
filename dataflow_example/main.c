#include <stdint.h>
#include <stdlib.h>

int switches(int cond, int value);
int ifs(char *buf, int len);

int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
    if (Size < 13) return 0;
    int res = switches(Data[11], Data[12]); 
    res += ifs(Data, Size);
    return res;
}