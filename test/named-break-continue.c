int printf(const char *, ...);
int main(void) {
	int n = 0, m = 0, k = 0, d = 0;
	outer: for (int i = 0; i < 5; i++) {
		for (int j = 0; j < 5; j++) {
			if (j == 3) continue outer;
			if (i == 3) break outer;
			n++;
		}
	}
	a: b: while (1) {
		sw: switch (m) {
		case 0: m = 1; break sw;
		case 1: m = 2; continue a;
		default: break b;
		}
		m += 10;
	}
	rows: do {
		int j = 0;
		while (1) {
			_Defer d++;
			if (++j == 2) continue rows;
			if (k == 2) break rows;
		}
	} while (++k < 10);
	/* a label on a loop is still a goto target, and plain break is unchanged */
	int g = 0;
	again: for (;;) { if (g++ < 2) goto again; break; }
	printf("%d %d %d %d %d\n", n, m, k, d, g);
	return 0;
}
