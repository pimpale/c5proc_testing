struct s {
	int a;
	const char *p;
	struct s *next;
	int b : 3;
	int arr[4];
	int (*f)(int, char *);
	struct inner { int x; } in;
	union { int u1; struct { char u2, u3; }; };
};
struct s {
	int a;
	const char *p;
	struct s *next;
	int b : 3;
	int arr[4];
	int (*f)(int, char *);
	struct inner { int x; } in;
	union { int u1; struct { char u2, u3; }; };
};
union u { int i; float f; };
union u { int i; float f; };
enum e { A, B = 5, C };
enum e { C = 6, A = 0, B = 5 };
enum f : short { X = 1, Y };
enum f : short { X = 1, Y };
enum big { BIG = 0x100000000 };
enum big { BIG = 0x100000000 };
struct s x;
enum big g = BIG;
int main(void) {
	struct s { int a; };
	struct s { int a; };
	struct s y = {A + C + Y};
	return y.a + x.u3 + sizeof(enum f) + sizeof(BIG);
}
