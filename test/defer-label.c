void put(int);

void f(int c) {
	_Defer {
		for (int i = 0; i < 2; i++) {
			if (i == 0)
				goto skip;
			put(i);
		skip:
			put(2);
		}
	}
	if (c)
		return;
	put(3);
}
