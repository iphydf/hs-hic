void print_float(float *pf) {
    return;
}

void test() {
    int32_t i;
    int32_t *pi;
    pi = &i;

    /* This should be a refined type error */
    print_float((float *)pi);
}