
typedef void my_cb(void *userdata);
struct My_Callback { my_cb *cb; void *userdata; };
struct Callbacks { struct My_Callback cbs[10]; };
struct My_Data { int x; };
void my_int_handler(void *p) { int *pi = p; }
void my_data_handler(void *p) { struct My_Data *pd = p; }
void use_cbs(struct Callbacks *cbs, int id) {
    struct My_Callback *handler = &cbs->cbs[id];
    handler->cb(handler->userdata);
}
void f() {
    int some_int = 3;
    struct My_Data some_data = {3};
    struct Callbacks cbs;
    cbs.cbs[0].cb = my_int_handler;
    cbs.cbs[0].userdata = &some_int;
    cbs.cbs[1].cb = my_data_handler;
    cbs.cbs[1].userdata = &some_data;
    cbs.cbs[1].userdata = &some_int; // SHOULD FAIL
    use_cbs(&cbs, 0);
}
