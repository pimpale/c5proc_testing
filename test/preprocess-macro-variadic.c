#define a(fmt, ...) f(fmt, ## __VA_ARGS__)
#define b(fmt, args...) f(fmt , ## args)
#define c(fmt, ...) f(fmt __VA_OPT__(,) __VA_ARGS__)
#define d(x, ...) __VA_OPT__(x ## x __VA_ARGS__) end
#define EMPTY
a("a") a("a", 1, 2) a("a",)
b("b") b("b", 3)
c("c") c("c", 4, 5) c("c",) c("c", EMPTY)
d(a) d(q, 1)
#define e(...) f(x, ## __VA_ARGS__)
e() e(EMPTY) e(1)
