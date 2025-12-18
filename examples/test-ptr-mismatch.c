void test() {
    int32_t i;
    float f;
    int32_t *pi;
    float *pf;

    pi = &i;
    pf = &f;

    /* This should be a refined type error even if C allows the cast */
    pf = (float *)pi;
}
