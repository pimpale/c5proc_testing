# C5 Programming Language

C5 is an attempt to make "C with templates" in a well thought-through way.
We want to have a small compiler, simple semantics, and to iron out many of the warts of C.

There are many "modern" C like languages to draw from. To name a few:
* C3 (of course)
* Zig
* Odin
* Jai

C5 occupies a much closer spot to C than any of the above.
1. No name mangling (unless explicitly opted into)
2. Separate TU compilation and build steps.
3. Classic C-like syntax (very high source compatibility, with some limited exceptions).

It is more of a "C dialect" than a separate language. That being said, some changes will likely need to be made to code being ported (although this can be done programmatically).
It is based off of the C23 standard, but adopts some features from C29.

## Features

### Named Arguments

The first feature is that we permit naming arguments. Named arguments must come after all positional arguments. For example:
```C5
int foo(int a, int b, int c, int d);

int main() {
    foo(1, 2, .d=4, .c=3);
}
```

It is an error to give an argument both positionally and by name, or name a parameter twice, or leave a non-implicit parameter unfilled.

The parameter names that are used come from the declaration that is visible at the call site (usually the one in the header). 
Named arguments cannot be used for parameters that don't have names.

### Structured Polymorphism based on Typeclasses

We introduce the following keywords for structured polymorphism: `forall`, `exists`, `mono`, `erased`.

Forall and exists introduce type parameters:
* `forall`: The equivalent of `template` in C++, introducing type parameters.
* `exists`: Introduces a type parameter which is consistent within the struct, but can be omitted elsewhere.

Mono and erased control monomorphization:
* `erased`: fully type erased polymorphism, equivalent to a C function using void pointers. No name mangling is applied.
* `mono`: monomorphizes, generating many copies of the struct or function.

The key thing to note is that these are not duck typed. C5 requires passing vtables to both monomorphized and type erased functions to make use of the type parameters.
This enables type checking to be much simpler than C++.

| Context | erased | mono | 
|---|---|---|
| struct| the struct cannot change layout no matter what arguments are passed. | the struct may change layout depending on what arguments are passed |
| function| one function body will be emitted. The function cannot change behavior based on the type, and has no knowledge of the types internal structure, or even its size. The object name does not contain any angle brackets | the function implicitly has access to the size, alignment, etc of the type. Many function bodies are generated. |
|constant| One object is generated | Many copies of the object are generated |


We'll give a demo, starting with `forall`:

In C++, you could do:
```C++
template<typename T>
T add(T a, T b) {
    return a + b;
}
```

Instead, in C5 you must use vtables:
```C5
forall<type T>
typedef struct {
    T (*add)(T, T);
} Add;

mono forall<type T>
T add(T a, T b, Add<T> add_vtable) {
    return add_vtable.add(a, b);
}
```

Observe that the struct can be merely `forall` since it only contains pointers, and thus its layout is independent of the type variables.

However, we needed to use `mono forall` on `add` here since its function body will depend on its argument (returning a struct works differently than returning an int).

We can do:
```C5
forall<type T>
T* add(T* a, T* b, Add<T*> add_vtable) {
    return add_vtable.add(a, b);
}
```

This generates only one body, one that is not name mangled, and can be called from C trivially.
This C code is equivalent:
```C
typedef struct {
	void* (*add)(void* a, void* b);
} Add;

void* add(void* a, void* b, Add add_vtable) {
	return add_vtable.add(a, b);
}
```

In `erased` code, you cannot use the variables to instantiate a mono body, since instantiation requries information that doesn't exist at this point, like the size and alignment of the type.
You can however instantiate mono structs behind pointers. Eg, declaring a variable like `*Vec<T>` is fine in erased code, as long as you don't try to access it. 


We'll get to `exists` in [a later section](#existential-types).

### Implicit Arguments

Obviously, passing around many vtables will get noisy. Thus, we need a way to reduce noise associated with them.
Our solution is implicit arguments. 

```C5
mono forall<type T>
T add(T a, T b, implicit Add<T> add_vtable) {
    return add_vtable.add(a, b);
}
```

Note that implicit parameters are just regular parameters in the ABI. Their main use is simply ergonomics, in order to reduce noise from repeatedly passing lists of vtables.
The variadic arguments always come last, and can never be implicit.
Naming a function without calling it gives a function pointer where the implicit parameters are converted to normal parameters.

The rule is that positional parameters fill only the parameters that are not implicit, in order. Implicit parameters must be either inferred or provided by named arguments.

Then:
```C5

int addInt(int a, int b) {
	return a + b;
}

int main() {
    given Add<int> add_int = { .add = addInt };

    // here, add is the monomorphized function in the prior code block
    add<int>(1, 2);
}
```

As long as there is at least one value of that type in scope declared with `given`, it will be selected during the function call. 
The most lexically recent will always be selected.
Implicit function arguments have `given` automatically.

Another example:

```C5
double addDouble(double a, double b) {
    return a + b;
}

given const Add<double> ADD_DOUBLE = { .add = addDouble };

int main() {
    // uses ADD_DOUBLE 
    add<double>(1.0, 2.0);
}
```

The following example shows what happens if there are two contenders:
```C5
int addInt(int a, int b) {
	return a + b;
}

int addIntTrapping(int a, int b) {
 int out;
 if(ckd_add( &out, a, b)) {
     exit(1);
 }
 return out;
}

int main() {
    given Add<int> add_int = { .add = addInt };
    given Add<int> add_int_trapping = { .add = addIntTrapping };
    // uses add_int_trapping
    add<int>(1, 2);

    { 
        // lexically scoped declarations override
        given Add<int> given_add = add_int;

        add<int>(1, 2); // used add_int (through given_add)

        // can directly specify overrides
        add<int>(1, 2, .add_vtable=add_int_trapping);
    }
}
```

You can also use `mono forall` givens:
```C5
mono forall<type T>
given const Eq<T> BYTE_EQ = { .eq = byte_eq<T> };

int main() {
   assert_equal<int>(1, 1); // uses BYTE_EQ<int>
   assert_equal<double>(1.0, 1.0); // uses BYTE_EQ<double>
}
```

Beware of things like these:
```
mono forall<type T>
given T x;

add<int>(1, 2); // probably crashes at runtime, but compiles.
```

Another footgun is duplicate implicit arguments of the same type. They will end up resolving to the exact same variable.

### Const Polymorphism

In C, we have const pointers: 
```c
int strlen(const char*);
```
The const is basically just to document permission, and can easily be casted away. Few optimizations can be made on its basis.
However, it has an annoying property that we see in functions like strchr:
```c
// should it accept const char* instead?
char* strchr(char *in, int c)
```
The constness of the output should depend on the constness of the input. `strchr` does not modify its input, but the user may want to. 
Thus, returning a const char*  is inappropriate when the input is not const. However, making it a normal char* forbids it from being used with const input.
C fixes it using _Generic:
```c
#define strchr(s, c) _Generic((s), \
    const char *: (const char *)(strchr)((s), (c)), \
    char *:       (strchr)((s), (c)) \
)
```
This is clearly a pretty suboptimal solution.
The alternative syntax is:
```c5
forall<constness C>
C char* strchr(C char* in, int c);
```
This has essentially the same behavior, but is better integrated with the polymorphism system declared earlier.

### The Array and Slice types

C5 has three different kinds of entities that may be indexed with []:
1. Classical C arrays: declared as `int x[5];`. These undergo decay in parameters, as before.
2. Proper array types declared as `array<int, 5> x;`. These can be passed and returned by value, like arrays in structs.
3. Finally, a slice type written as `slice<int>` Under the hood, it is a two element struct, with a pointer, and a length field.

#### C5 Arrays

C5 arrays also decay to pointers for indexing purposes. The only difference is that they do not undergo parameter adjustment when listed in function parameters or return types. Thus, they can be passed and returned by value.
Similarly, they are copied by value if doing `x = y`. 

However, they do decay if passed to a function accepting a pointer.

#### Slicing
The primary purpose of the slice is to enable syntax sugar around dynamic slicing. It is explicitly a view of the data. Thus, passing it by value only passes the underlying array by reference.
It also can basically replace the null terminated string in most contexts. slice<char> is pretty good. 
You should use unicode functions where needed though, as chars are not code points.
A slice's length can be accessed via .length, and the underlying data pointer via .data.
Pointer arithmetic and indexing on a slice works as if on the .data component.

Slices cannot be initialized via array initializer syntax though, as this conflicts with their struct based nature: 
```C5
slice<int> x = {0}; // not a slice of [0]! Instead, a null slice (null ptr, 0 length)
```

A slice can be created explicitly via struct construction, or through slicing:
The specific slicing syntax that we can use (applies to slices, pointers and arrays) is p[n ... m] and p[... m], when we care about a 0 indexed prefix.
Slice length for p[n ... m] is m - n + 1. Thus, p[0 ... len - 1] is safe even when len is 0.
p[n ...] and p[...] are also permissible when indexing a slice, C5 array, or C array, for a slice to the end.
Slice ranges are inclusive. This is the same syntax used in c29 case ranges.

The actual way to get a slice of [0] is:
```C5
array<int, 1> y = { 0 };
slice<int> x = y[...];
```

Generally speaking there are no implicit conversions to slices.

### String Literals

C5 supports both C style null terminated strings and Pascal style strings with a separate length. The latter are slices or arrays. 

C5 supports two new prefixes before strings:
* `p"`: pascal style. No null terminator.
* `c"`: c style, with a null terminator.
Both of these can be combined with other prefixes, eg `pL`, or `cu8`. The p or c must come before the other encoding flags.

It also supports a new prefix:
* `n"`: native encoding. This is the default in C, unless some prefix is applied.

These prefixes can be used from both C compatible and C incompatible code.

In C-incompatible mode (described below), plain unprefixed string literals are pascal style. In C-compatible, they are c style, as expected.

Additionally, in C-incompatible mode, all strings (both pascal and c) are in UTF8 (the equivalent of c29's u8 strings) unless prefixed with `n`. This means strings are of type unsigned char instead of normal char. Both types of string literal in C-incompatible mode also are C5 array typed. To give an example:
```C5
// c compatible mode
char x[2] = "a";
// c incompatible mode
array<unsigned char, 1> x = "a";
```

One footgun here is that in C-incompatible mode, things like `puts("hi")` will read past the end of the string (although it can warn or error due to the encoding mismatch), since there is no null terminator. It is necessary to prefix them: `puts(cn"hi")`. It is generally recommended to use the C5 standard library primitives instead.

### Destructuring and extending switch
We introduce destructuring syntax for variable assignments and switches.
The syntax broadly mimics ML-family languages, where destructuring appears similar to the designated initializer syntax.
```C5
struct Point {
  int x;
  int y;
};

{.x=int x, .y=int y} = get_point();
// or simply
{auto x, auto y} = get_point();
```

Each binding is introduced with a type name or auto. This keeps parsing C5 simple with limited lookahead.

To avoid binding certain fields, you can write:
```C5
{int, auto y} = get_point();
```
This mirrors how unnamed parameters work in functions.
Nested destructuring is also possible.

But, the standout use case is in switch. We permit switching on structs as well as numbers. First match wins.
```C5
switch(get_point()) {
  case {1, int y}: {
    return y;
  }
  case {2, int y}: { 
    printf("hello %d", y);
    break;
  }
}
```

The rules are that if you use destructuring in a switch where you bind variables, you must use a block for the case. Your bound variables exit scope at the end.
You can destructure unions in switches. This allows you to emulate tagged unions. However, there are no rules for accessing the wrong case. You must be careful.


The main reason for importing this feature is to get multiple return values. 
Specifically, the greatest ergonomic improvements come from error handling:
```c5

typedef enum {
    ERR_OK = 0,
    ERR_NOT_FOUND = 404
    // ... other errors ...
} FileSystemErr;

Result<char*, FileSystemErr> readFile(char* filename) {
    // ...
}


// ...
{ResultKind kind, char* data, FileSystemErr err} = readFile("foo.txt");
if(kind != RESULT_OK) {
  return err;
}

// or, to use pattern matching:
char* data;
switch(readFile("foo.txt")) {
  case {.kind=RESULT_OK, .data=auto val}: {
    data = val;
    break;
  }
  case {.kind=RESULT_ERR, .err=auto e}: {
    return e;
  }
}

```

These names that are introduced into the scope are actually aliases for the struct members. 
Thus, things like bitfields should still have the same effect.

Destructuring works the following way:
```C5
{int x, int y} = get_point();
dosomething(y);
// desugars to
Point p = get_point();
dosomething(p.y);
```

Thus, bitints and such work as expected.

### Existential Types

While type parameter lists introduced by `forall` are certainly the most useful, `exists` also is a useful construction that allows creating objects that hide their implementation, akin to Rust's `dyn Trait` and `impl Trait`.

#### Erased Types in Structs

This is best illustrated with the example of an abstract "allocator".
Without existential types, a fully typed out allocator could look like this:
```C5
struct Allocator {
    void* data;
    void* (*allocate)(void*, size_t);
};
// or
forall<type AllocatorData>
struct Allocator {
    AllocatorData* data;
    void* (*allocate)(AllocatorData*, size_t);
};
```
The former is the traditional C way of typing this struct. It doesn't have type safety. void* can point to whatver.
The latter has type safety, but the downside is that it has to carry around an extra AllocatorData type argument. 
We can't add two different allocators of the latter to a vector, even if their layouts and use are exactly the same:
```C5
Allocator<LibCAllocator> la = get_libc_allocator();
Allocator<ArenaAllocator> aa = get_arena_allocator();

// can only store one kind of allocator (for no reason)
Vec<Allocator<LibCAllocator>> v = ...;
```

The solution is existential types:
```C5
exists<type AllocatorData>
struct Allocator {
    AllocatorData* data;
    void* (*allocate)(AllocatorData*, size_t);
};

// The existential types are not mentioned
const Allocator la = get_libc_allocator();
const Allocator aa = get_arena_allocator();

// can now store them in containers
Vec<Allocator> v = ...;
```

A key fact about existential types is that two different allocator values members' types are different: typeof(la.data) != typeof(aa.data). 
Essentially, every value of an existential type gets its own unique type variables that are not interchangeable.
Thus, existential types come with restrictions:
* When you initialize the struct, or create a new value of the struct, the types are checked for consistency. You cannot use one type for E in one member, and another in another member.
* Accessing a member of the struct that contains the existential type (as both a.data and a.allocate do) is only possible when X can't be changed when it's in use. 
    * Eg, suppose that I call reset_allocator() in between accessing a.data and a.allocate.
    * So, the struct containing the existential must be `const`, or accessed through a chain of const pointers. 
    * In general, changing the value of an existential types between reads is undefined behavior.
* Members of the struct that don't mention the existential type can be accessed freely.
* Alternatively, the existential type can be destructured. This is always possible.

#### Monomorphized Types in Structs

The above makes use of erased existential types, where the type is only referred to behind a pointer. If you are willing to monomorphize, you can directly include the erased type:
```C5
mono exists<type S> 
struct Allocator {
    const AllocatorVT* vt; // the functions in the vtable take Allocator* as an argument
    alignas(16) S state;
};

Allocator* a = make_arena(heap, 64 * 1024);
a->vt->alloc(a, 128);
```

The requirement is that the existential type come at the end of the struct. This is because it is unsized, like a flexible array member.
Like other structs with flexible array members, they cannot be placed in other structs or arrays unless behind a pointer.
You are required to put an alignas on the flexible member if you want to be able to access it, so that the offset becomes known.
It is legal to leave it unaligned, but then you will not be able to access that member.
In our example, this is how the functions in vt can access it. Doing this puts structs with an unsized member like this on the same footing as flexible array members now.

Like flexible array members, copying and sizeof do not include the size of the unsized struct. This is for consistency.

#### Existential Types on Functions

Planned, but not implemented in v1.

### Miscellaneous smaller changes and notes:

* sizeof and typeof require parentheses around their arguments.
* return statements take initializer lists in the grammar, enabling using struct initializers in return position. 
* C29's defer is implemented (exactly the way it is in C29).
* Range syntax for cases is identical to the range syntax for slices (described in C29). 

## A closer look at C5 polymorphism

`forall` may precede the following:
* struct declarations
* functions
* variable declarations.

`exists` may precede the following:
* struct declarations 

If `forall` and `exists` are used together, `exists` must always come after `forall`. You cannot repeat forall and exists declarations.

`mono` and `erased` can only come before the first `forall` or `exists` clause. If neither is specified, `erased` behavior is assumed. Mono or erased before a non-polymorphic function is an error.
For `mono` functions and variable declarations, the compiler will generate a family of related values for each instantiation. 
For `erased` functions and variable declarations, the compiler will generate at most one.

Both `forall` and `exists` use the same type-parameter-list. This list is enclosed in angle brackets, and must contain one or more parameters. See the example below:
```
forall<type A, size B, constness C>
```
Each parameter must be either `type`, `size`, `constness`.

Note that `constness` will always be erased, even if `mono` is applied. 

A `<` following an identifier opens an argument list only if that identifier names a `forall` entity in the current scope, or is one of the keywords `array` and `slice`; otherwise it is the less-than operator.
Inside an argument list, a `>>` token closes two lists, so `Vec<Vec<int>>` is valid. A `size` argument that contains a top-level `>` or `>>` must be parenthesized, e.g. `array<int, (N > 4 ? 8 : 4)>`.


### Type parameters
Type parameters introduced by `erased` are incomplete. You can have pointers to them, but you cannot know their size or alignment.
Type parameters introduced by `mono` can have their size and alignment known. It is possible to access their bytes directly, permitting byte-level equality comparisons. 
However, their members are unknown, and duck typing C++ style doesn't work. They cannot be treated as integers, for instance, (even if they are).

Even if inside a mono context, and you are trying to initialize a struct, you must treat the initializer of that type variable as a leaf. For example, in this example:
```C5
mono forall<type T>
struct Pair {
    T first;
    T second;
};

// in a mono context function:
mono forall<type T>
void foo(T a) {
    struct Pair<T> p = { a, a };
}
```
In C, you can do brace elision to initialize subobjects. However, we ban this in the context. For example, if T were `struct {int i; int j}`, then initializing it with {1,2,1,2} would work. However, in C5 in this context, you can't do this. Each member that is a type variable must be initialized by a discrete expression (so {{}, {1, 2}} would work).

### Constness parameters
Constness has two values: `const` and `mut`. Mut is the default. It captures the difference between a type having const and not. It does not capture other modifiers like atomic, volatile, or restrict.

### Size parameters
C5 offers a `size` parameter that allows polymorphic constructions to abstract over array sizes.
In `erased` contexts, this value is totally erased. It is not legal to access N or measure the size of the array.
In `mono` functions, this value is accessible as a constexpr of type size_t. 
Specialization failures (eg via _Static_assert), unlike C++, are fatal errors, and will be raised at the place of instantiation, with a note pointing back to the line where the failure happened in the polymorphic body.

Size parameters are never passed as a runtime parameter.

### Example: Collections 

Suppose we have a vector of type T which maintains an allocator.
If we wanted to implement the Collection trait for it, we could do the following:

```c5

// there are no higher kinded types or associated types.
// However, it is relatively simple to list both self and elem in the forall type param list.
forall<type Self, type Elem>
typedef struct {
    size_t (*len)(const Self*);
    Elem*  (*at)(Self*, size_t);
} CollectionVT;

// functions can use Collection while being ignorant about the actual type like:
forall<type C, type E>
E* first(C* c, implicit CollectionVT<C, E> coll_vt) { return coll_vt.at(c, 0); }

// We can implement Collection for vec by defining a global variable.
mono forall<type T, type A>
given const CollectionVT<Vec<T, A>, T> COLL_VEC = { .len = vec_len<T, A>, .at = vec_at<T, A> };

// now if we want to use first for a vec of ints, we can:
int main() {
    Vec<int, LibcAllocator> x = new_vec();
    vec_push(&x, 1);

    // automatically infers type and uses the selected instance
    // the most recent match that satisfies constraints is used.
    int* f = first(&x);
}
```

### Implicit Arguments and Type Inference

Suppose we have a call `f<type_args>(args, .overrides=overrides)`. Then:
1. First, explicit type arguments take precedence. Either the list is omitted, or all arguments must be written, using `auto` for those to be inferred.
2. Second, we infer from arguments. We unify the parameter type with the argument type. Before unification, the argument undergoes lvalue->rvalue conversion, and pointer decay if a standard C array. Top level qualifiers are dropped. 
   * Implicit conversions are not considered, except for constness conversions. Const can also be captured via a constness qualifier. 
   * Conflicting bindings are an error.
   * We infer from left to right at the call site. Ordering of named parameters matters for whether resolution succeeds or not.
3. We then unify the return type of the call with the expected type, but only in the contexts: 
    * the right side of =
    * the operand of return
    * the whole initializer of a declaration with a concrete type.
    * In other contexts, this is skipped.
4. Finally, we search for givens for the remaining implicit parameters:
    * We search all candidates in scope, most recent first. 
    * The first candidate whose type unifies with the parameter is selected.
    * There is no backtracking.


In both `erased` and `mono` contexts, the inference proceeds treating the type parameters as an opaque type. It only happens once per definition, not once per instantiation.

### Linking
Each instantiation of a mono function or variable is a single entity across the program.

It has a canonical name:
* One space after each comma.
* all typedefs resolved. Structs have a space but no newline between members. The last member has no space between the semicolon and the end bracket.
* size arguments as decimal numbers
* mut and const arguments erased. They leave an empty slot.

Eg, if we have:
```C5
mono forall<type T, size N, constness C>
C array<T, N> foo(C array<T, N> in) {
    return in;
}
```
Then a fully qualified instantiation might be 
```
foo<struct {int x; int y;}, 5, >
```

## Controlling C compatibility

Different files have different requirements for classical C compatibility. There are two modes for c5:
1. C compatible
2. C incompatible

In reality, both are slightly incompatible with C. But the former is far more compatible.
Mode applies per file. When the file being parsed or included ends in .c or .h, it is parsed in C compatible mode. If it ends in .c5 or .h5 it is parsed in C incompatible mode.

### C5 C-Incompatible Mode

In idiomatic C5, the following are banned:
1. VLAs
2. _Generic
3. Normal C array

Also, like in C++, struct names and enum names are accessible without prefix "struct", "enum", or "union". This follows C++ rules.

The list of reserved keywords in C5 incompatible mode is:
* mono
* erased
* forall
* exists
* given
* implicit
* array
* slice

There are also contextual keywords:
* As the first word of a parameter in a forall or exists parameter list
    * type
    * size
    * constness
* As the argument for a constness parameter
    * mut


### C5 C-Compatible Mode

When parsing in C compatible mode, the banned features are kept available. Additionally, in C compatible mode, all novel keywords are of the form _Forall, _Exists, etc.
You can do:
```C
#include <c5.h>
```
to be able to use the reserved keywords. (These keywords work in C-incompatible mode as well, in case you included c5.h in C-compatible mode).

`sizeof` requires parentheses here too.