# c5lang.md: spec TODOs

Places where `c5lang.md` still leaves a choice open or needs a sentence or more of new
text. Each item says what the compiler currently does, so the spec can either adopt that
or the compiler can be changed. Items are located by section, since line numbers drift.

Resolved since the first version of this list (in the spec or by a small edit): given
priority order, the Paterson rule wording, pointer premises, temporaries not being givens,
the positional call in the derived-instance desugaring, slice operators, the
`slice<T>` to `slice<const T>` conversion, slicing a plain pointer without an upper bound,
the slice member names, the string prefix list, the type of `p"…"` in C-compatible mode,
destructuring only in blocks, the reason existentials need destructuring, tag hiding,
parenthesized size arguments, what `c5.h` defines, step 3 only binding unknown parameters,
and `sizeof` parentheses being required only in C-incompatible mode.

## Givens and implicit arguments

- [ ] **Derived Instances — address-of rule.** Say what happens when a given `T*` and a
  given `T` could both satisfy a `T*` parameter. *Implemented:* ambiguous if they are in
  the same scope.
- [ ] **Derived Instances — static initializers.** State that a derived instance cannot
  appear in a static initializer (it needs a call).
- [ ] **Derived Instances — qualifiers.** Say that taking the address of a `const` given
  only satisfies a pointer-to-const parameter, and that top-level qualifiers are ignored
  for by-value parameters. *Implemented:* as described.
- [ ] **Derived Instances — Paterson measure.** "More complex" is not defined.
  *Implemented:* count type constructors and variables, after stripping one pointer level
  from the premise; additionally no type variable may occur more often in a premise than
  in the result.
- [ ] **Inference step 4 — givens can bind type arguments.** Say that matching a given may
  determine type arguments still unknown after step 3. *Implemented:* yes, so `first(&x);`
  works as a plain statement with no expected type.
- [ ] **Implicit Arguments — `forall` givens.** State that every type parameter of a
  `forall` given must appear in its type (for a given function, in its result type).
  *Implemented:* an error at the declaration otherwise.
- [ ] **Named Arguments — function pointers.** *Implemented:* named arguments are allowed
  through a function pointer, using the parameter names of the pointer's type; implicit
  resolution applies only to direct calls of a declared function.

## Type inference

- [ ] **Step 3 — "the call is the whole expression".** Define it. *Implemented:* the
  expression must start with the name of the polymorphic function, and the call's closing
  parenthesis must be followed by `;`, `,`, `)` or `}`.
- [ ] **Step 2 — C5 arrays.** Say that a C5 array argument unifies as an array (not a
  pointer) against a parameter of C5 array type. *Implemented:* yes.

## Arrays, slices, strings

- [ ] **C5 Arrays — where they decay.** List the contexts. *Implemented:* a C5 array is
  used as a whole when assigned, passed to a parameter of array type, returned, used to
  initialize an array or an `auto` variable, or under `sizeof`/`typeof`; everywhere else
  it decays to a pointer to its first element.
- [ ] **C5 Arrays — ABI.** State that an `array<T, N>` is passed and returned like a struct
  containing it.
- [ ] **Slicing — details.** Say that bounds are not checked, and that slicing a `const T*`
  gives `slice<const, T>`.
- [ ] **String Literals — remaining type questions.** State that an empty string is a
  zero-length array, whether elements are `const` (*implemented:* not const, as in C), and
  that `L`/`u`/`U` literals in C5 files are also unterminated C5 arrays. Say that adjacent
  literals must agree on both the terminator and encoding prefix where they specify them.

## Constness and variance

- [ ] **Opaque structs.** The spec says an opaque struct's parameters are invariant unless
  marked. *Implemented:* a `forall` struct cannot be instantiated before its definition is
  complete, even behind a pointer, so markers on an opaque declaration have no effect yet.
- [ ] **C-compatible mode.** Say whether the new conversions (function pointers, and
  pointers to pointers such as `int **` to `const int *const *`) apply in `.c` files.
  *Implemented:* they apply in both modes.
- [ ] **Conditional operator.** Say what `c ? a : b` is when the operands are const
  variants. *Implemented:* the operands must have compatible types, as before.
- [ ] **Uncaptured qualifiers other than const.** *Implemented:* a type parameter never
  captures any qualifier; a `volatile` pointee passed for a plain `T*` is rejected when
  the argument is converted.
- [ ] **Explicit type arguments.** *Implemented:* a const-qualified argument for a type
  parameter, as in `Vec<const int>`, is an error.
- [ ] **Mono instances.** *Implemented:* const variants of a type argument share one
  instance, so `f<Foo<mut>>` and `f<Foo<const>>` are the same function.
- [ ] **Given specificity.** A `forall<constness C>` given and a given for one constness
  are not ordered by either tie-break. *Implemented:* ambiguous if both match.

## Destructuring and switch

- [ ] **Bindings — types.** Say whether a typed binding must match the member's type.
  *Implemented:* it must be compatible; qualifiers on the binding are added.
- [ ] **"Limited lookahead".** `{int x, int y} = f();` is told apart from a compound
  statement by looking for `=` after the matching `}`, which is unbounded lookahead.
  Either accept that or change the syntax (for example a leading keyword).
- [ ] **Positional and designated elements.** Say that positional elements follow the
  members in order, that a positional element after a designated one continues from the
  member after it (as in initializer lists), and whether arrays can be destructured
  (*implemented:* no).
- [ ] **Case patterns.** Say which constants are allowed (*implemented:* any constant
  expression against a scalar member, and inclusive ranges `lo ... hi`), that fallthrough
  between cases works as in C (*implemented:* yes), that a case with no bindings does not
  need a block, and that `default` is allowed.
- [ ] **Case ranges on integers.** Say that ranges are tested in order before the
  single-value cases, and whether overlapping ranges are an error (*implemented:* overlap
  is diagnosed only for ranges of up to 1024 values).
- [ ] **Aliases.** State that the destructured value is copied once, so writes through a
  binding do not affect the original.

## Existentials

- [ ] **Opening.** Add that bindings from two destructurings of the same value do not mix,
  and that the opened types can be named with `typeof`.
- [ ] **`mono exists`.** *Implemented:* `mono exists<…>` alone is an error;
  `mono forall<…> exists<…>` is accepted with the existential parameters erased. Say
  whether the second form is intended for v1.

## Linking and modes

- [ ] **Static locals of mono functions.** They are per translation unit even when the
  function itself is comdat, so two translation units see different objects. Either
  specify that or require them to be merged too. The same question applies to instances
  of `static` mono declarations (*implemented:* local to each translation unit).
- [ ] **Canonical names.** Give the spelling of named structs (*implemented:* the tag
  alone, without `struct`), of enums (*implemented:* the underlying integer type), and of
  `array<T, N>` and `slice<T>`.
- [ ] **Bans.** Say the bans are syntactic and per file: a C array type that comes from a
  `.h` header can still be used from a `.c5` file.
- [ ] **Toolchain note.** The Linking section depends on a QBE with `comdat` support (the
  `qbe-comdat` fork). Worth a sentence somewhere, since stock QBE 1.3 rejects the output.
