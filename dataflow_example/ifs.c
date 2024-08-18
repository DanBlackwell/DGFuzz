#include <string.h>

int inner_ifs(char in) {
    if (in > 125) {
        return 1;
    }
    return 0;
}

int ifs(char *buf) {
    int res = 0;

    if (buf[0] == buf[1]) {
        if ((buf[2] & buf[3]) == 0x3) {
            res = 4;
        } else if (buf[4] < -120) {
            if (*(int *)(&buf[5]) > 100000) {
                res = 6;
            } else if (memcmp(&buf[3], &buf[6], 3) == 0) {
                res = inner_ifs(buf[10]);
            } else {
                res = 8;
            }
        }
    }

    return res;
}