size_t net_pack_bool(uint8_t *bytes, bool v)
{
    bytes[0] = v ? 1 : 0;
    return 1;
}
