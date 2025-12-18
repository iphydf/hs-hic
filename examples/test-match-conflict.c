typedef enum Tag {
    TAG_I,
    TAG_F
} Tag;

typedef union Data {
    int32_t i;
    float f;
} Data;

typedef struct Container {
    Tag tag;
    Data d;
} Container;

void test(Container *c) {
    switch (c->tag) {
    case TAG_I: {
        c->d.f = 1.0f;
        break;
    }
    case TAG_F: {
        c->d.i = 10;
        break;
    }
    }
}
