# QBE issues found while developing C5

Issues in QBE (not cproc) found during this work, with reproducers, so
they can be reported upstream. All were observed with QBE 1.3 on
x86_64 Linux.

## 1. Conditional move reads flags clobbered by a GOT address computation

**Type:** miscompilation (wrong code, crashes at run time).

When a `phi` chooses between two addresses and one of them is an
`extern` symbol plus an offset, QBE converts it to a conditional move.
The address of the extern symbol is computed between the comparison and
the `cmov`, with an `add` that overwrites the flags. The `cmov` then
tests the flags of the `add` instead of the comparison.

`cmov.ssa`:

```
export function l $f(l %p) {
@start
	%c =w cnel %p, 0
	jnz %c, @yes, @no
@yes
	%a =l add %p, 24
	jmp @join
@no
	%b =l add extern $tok, 8
@join
	%r =l phi @yes %a, @no %b
	%v =l loadl %r
	ret %v
}
```

`main.c`:

```c
long tok[4] = {0, 42, 0, 0};
long f(long *);
int main(void) { return f(0) == 42 ? 0 : 1; }
```

```
$ qbe cmov.ssa > cmov.s && cc cmov.s main.c && ./a.out
Segmentation fault
```

Generated code for `f`:

```
	cmpq $0, %rdi
	setnz %cl
	movzbl %cl, %ecx
	movq %rdi, %rax
	addq $24, %rax
	cmpl $0, %ecx              # flags := (%p != 0)
	movq tok@gotpcrel(%rip), %rcx
	addq $8, %rcx              # overwrites the flags
	cmovz %rcx, %rax           # tests the flags of the addq
	movq (%rax), %rax          # loads from 24 when %p is null
	ret
```

With a symbol defined in the same file, QBE uses `leaq tok+8(%rip)`,
which does not affect the flags, and the code is correct.

**How it was found:** cproc compiled by itself (stage 2) crashed on
`x = p ? p->loc : tok.loc;` with struct operands, which cproc lowers to
a `phi` of the two addresses followed by a copy.

**Workaround in this repository:** `monoinst` in `mono.c` uses
`if`/`else` instead of a conditional expression.

**Likely fix:** in instruction selection or emission for the
conditional move, materialize the operands before the comparison, or
compute the extern address without changing the flags (for example,
`movq` from the GOT followed by `leaq 8(%rcx), %rcx`).

## 2. No way to emit symbols that the linker merges (weak or COMDAT)

**Type:** missing feature.

C5's `mono` instances (and C++-style inline functions and templates in
general) must be a single entity across the program, even though every
translation unit that uses one emits it. That needs weak definitions or
COMDAT groups on ELF (`.weak` or `.section ...,"axG",@progbits,sym,comdat`)
and `.weak_definition` on Mach-O.

QBE 1.3 has `export` and `section`, but no weak linkage. The flags
string of `section` can't be used to get a COMDAT group either, because
QBE quotes it:

```
section ".text.f" "\"axG\",@progbits,f,comdat"
```

becomes

```
.section ".text.f","\"axG\",@progbits,f,comdat"
```

which the assembler rejects.

**Current state in this repository:** instances are emitted as local
symbols in each translation unit, so function pointers to the same
instance compare unequal across translation units.

## 3. Quoted symbol names don't get the Darwin underscore prefix

**Type:** possibly intended behavior; worth confirming.

On `amd64_apple` and `arm64_apple`, QBE prepends `_` to ordinary symbol
names, but not to quoted ones: `$"add<int>"` is emitted as
`"add<int>"`, not `"_add<int>"`.

This matches GCC and Clang's treatment of assembler labels
(`__asm__("name")` is used verbatim), so it may be intended. But it
means a front end must add the `_` itself for names that need quoting,
or `dlsym("add<int>")`, which looks up `_add<int>` on Darwin, can't find
them.
