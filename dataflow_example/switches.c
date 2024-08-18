
int switches(int cond, int value) {
    int res = value;

    switch (cond)
    {
    case 0:
        res += value;        
        break;
    case 1:
        res += 55;
        break;
    case 2:
        res *= 15;
        break;
    case 3:
        res = -res;
        break;
    default:
        break;
    }

    return res;
}