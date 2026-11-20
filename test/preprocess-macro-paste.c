#define CAT(a, b) a ## b
#define XCAT(a, b) CAT(a, b)
#define one 1
CAT(foo, bar) CAT(one, one) XCAT(one, one) CAT(1, e3) CAT(<, <=) CAT(L, "s") CAT(., 5)
CAT(, x) CAT(x, ) [CAT(,)]
#define t(x, y, z) x ## y ## z
t(1,2,3) t(,4,5) t(6,,7) t(8,9,) t(10,,) t(,11,) t(,,12) [t(,,)]
#define obj x ## y z ## one
obj
#define hash_hash # ## #
#define mkstr(a) # a
#define in_between(a) mkstr(a)
#define join(c, d) in_between(c hash_hash d)
join(x, y)
#define both(x) x x ## _t #x
both(one) both(CAT(a, b) c)
