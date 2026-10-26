struct s {
	char c;
	alignas(16) char e;
};

void f(void) {
	struct s x = {0};
}
