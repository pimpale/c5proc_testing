enum f : unsigned char { X, Y };
enum g : unsigned long long { P, Q = 0xffffffffffffffff };
int a = X, b = Y, c = sizeof(enum f);
unsigned long long d = Q;
