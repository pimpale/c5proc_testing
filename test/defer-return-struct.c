struct s {
	long a, b, c;
};

struct s f(void) {
	struct s x = {1, 2, 3};
	_Defer x.a = 4;
	return x;
}
