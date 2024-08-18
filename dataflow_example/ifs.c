
int inner_ifs(char in) {
    if (in > 5) {
        return 1;
    }
    return 0;
}

int ifs(char *buf, int len) {
    int res = 0;

    if (len > 1 && buf[0] != buf[1]) {
        if (len > 2 && (buf[0] & buf[2]) == 0) {
            res = 4;
        } else if (buf[1] > 64) {
            if (len > 6 && *(int *)(&buf[2]) > 999) {
                res = 6;
            } else {
                res = inner_ifs(buf[0]);
            }
        }
    }

    return res;
}