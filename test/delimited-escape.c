char a[] = "\x{41}\o{102}\u{43}";
char b[] = "\x{1}2\o{7}7";
char c[] = u8"\u{e9}\u{1F600}";
unsigned short d[] = u"\u{1F600}\x{ffff}";
unsigned e[] = U"\u{10FFFF}\o{17}";
int f = '\x{7f}' + '\o{101}' + '\u{41}';
