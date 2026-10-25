void put(int);

void block(void) {
	_Defer put(1);
	_Defer put(2);
	{
		_Defer put(3);
		put(4);
	}
}

void loop(int n) {
	for (int i = 0; i < n; i++) {
		_Defer put(i);
		if (i == 1)
			continue;
		if (i == 2)
			break;
		put(10);
	}
}

int early(int c) {
	_Defer put(1);
	if (c) {
		_Defer put(2);
		return c;
	}
	return 0;
}

void backgoto(int n) {
again:
	{
		_Defer put(n);
		if (--n)
			goto again;
	}
}
