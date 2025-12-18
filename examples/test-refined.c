typedef enum Packet_Type {
    PACKET_I,
    PACKET_S
} Packet_Type;

typedef union Packet_Data {
    int32_t i;
    char *s;
} Packet_Data;

typedef struct Packet {
    Packet_Type type;
    Packet_Data data;
} Packet;

void handle(Packet *p) {
    switch (p->type) {
    case PACKET_I: {
        p->data.i = 10;
        break;
    }
    case PACKET_S: {
        p->data.s = nullptr;
        break;
    }
    default: {
        break;
    }
    }
}
