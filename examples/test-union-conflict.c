typedef union Data {
    int32_t i;
    float f;
} Data;

void test(Data *d) {
    d->i = 10;
    d->f = 1.0;
}
