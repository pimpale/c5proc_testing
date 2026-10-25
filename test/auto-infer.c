struct s {
	int x, y;
};
struct s mk(void);

auto g = 2.5;
static auto sg = 7L;

void f(void) {
	int arr[4];
	auto a = 1;
	auto p = arr;
	const auto c = 'x';
	auto b = {42u};
	auto st = mk();
	auto fp = mk;
	for (auto i = 0L; i < 3; i++)
		;
}
