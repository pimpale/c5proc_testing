#define F(x) [x]
#define G F
F(F(F(1))) G(2) G (3) F
(4) F
#define a b
#define b a
a b a
#define AA BB(
#define BB(x) <x>
AA 5)
#define f1(a) a*g1
#define g1(a) f1(a)
f1(2)(9)
#define str(x) #x
#define xstr(x) str(x)
#define both(x) #x x
both(F(G(1)   +  2)) xstr(__LINE__) __LINE__ str(__LINE__)
#define line __LINE__
line __COUNTER__ __COUNTER__ xstr(__COUNTER__)
_Pragma("omp parallel") after _Pragma("once")
