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
2. Seperate TU compilation and build steps.
3. Classic C-like syntax (very high source compatibility, with some limited exceptions).

It is more of a "C dialect" than a seperate language. That being said, some changes will likely need to be made to code being ported (although this can be done programmatically).

## Features

### Structured Polymorphism based on Typeclasses

We introduce the following keywords for structured polymorphism:
* `generic`: fully type erased polymorphism, equivalent to a C function using void pointers.
* `template`: monomorphizes, mangles names. 

The key thing to note is that these are not duck typed. C5 requires passing vtables to both generic and template functions to make use of the generic types.
This enables type checking to be much simpler than C++.

| Context | generic | template| 
|---|---|---|
| struct| the struct cannot change layout no matter what arguments are passed. | the struct may change layout depending on what arguments are passed |
| function| one function body will be emitted. The function cannot change behavior based on the type, and has no knowledge of the types internal structure, or even its size| the function implicitly has access to the size, alignment, etc of the type. Many function bodies are generated |

To give a demo:

In C++, you could do:
```C++
template<typename T>
T add(T a, T b) {
    return a + b;
}
```

Instead, in C5 you must use vtables:
```C5
generic<type T>
typedef struct {
    T (*add)(T, T);
} Add;

template<type T>
T add(T a, T b, Add<T> add_vtable) {
    return add_vtable.add(a, b)
}
```

Observe that the struct can be merely `generic` since it only contains pointers, and thus its layout is independent of the type variables.

However, we needed to use template on `add` here since its function body will depend on its argument (returning a struct works differently than returning an int).

We can do:
```C5
generic<type T>
T* add(T* a, T* b, Add<T*> add_vtable) {
    return add_vtable.add(a, b)
}
```

This generates only one body, one that is not name mangled, and can be called from C trivially.
This C code is equivalent:
```C
typedef struct {
	void* add(void* a, void* b);
} Add ;

void* add(void* a, void* b, Add add_vtable) {
	return add_vtable.add(a, b);
}
```

C5 eliminates _Generic, since this mechanism (and a later-discussed one) largely subsumes it.

### Implicit Arguments

Obviously, passing around many vtables will get noisy. Thus, we need a way to reduce noise associated with them.
Our solution is implicit arguments. The syntax mimics scala:

```C5
template<type T>
T add(T a, T b)(using Add<T> add_vtable) {
    return add_vtable.add(a, b)
}
```

Note that hidden parameters are just regular parameters in the ABI. Their main use is simply ergonomics.

It is forbidden to have more than one argument of the same type in the using list.

Then:
```C5

int addInt(int a, int b) {
	return a + b;
}

int main() {
    Add<int> add_int= { .add = addInt };
    add<int>(1, 2);
}
```

As long as there is one defined value of that type in scope declared with `given`, it will be selected during the function call. 
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
    given Add<int> add_int= { .add = addInt };
    given Add<int> add_int_trapping = { .add = addIntTrapping };
    // uses add_int_trapping
    add<int>(1, 2);

    { 
        // lexically scoped declarations override
        given Add<int> given_add = add_int;

        add<int>(1, 2); // used add_int (through given_add)

        // can directly specify overrides
        add<int>(1, 2)(using add_int_trapping); // used add_int_trapping
    }
}
```

You can also use incomplete types:
```C5
template<type T>
given const Add<T> ADD = { .add = templatedAdd<T> };

int main() {
   add<int>(1, 2); // uses ADD<int>
   add<double>(1.0, 2.0); // uses ADD<double>
}
```

Beware of things like these:
```
template<type T>
given T x;

add<int>(1, 2); // probably crashes at runtime, but compiles.
```

### Const Polymorphism

In C, we have const pointers: 
```c
int strlen(const char*);
```
The const is basically just to document permission, and can easily be casted away. Few optimizations can be made on its basis.
However, it has an annoying property that we see in functions like strchr:
```c
// should it accept const char* instead?
char* strchr(char *in, char c)
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
generic<constness C>
C char* strchr(C char* in, char c);
```
This has essentially the same behavior, but is better integrated with the polymorphism system declared earlier.

### The Array and Slice types

C5 has three different kinds of entities that may be indexed with []:
1. Classical C arrays: declared as `int x[5];`. These undergo decay in parameters, as before. (Can be toggled with pragmas)
2. Proper array types declared as `array<int, 5> x;`. These are passed and returned by value, like structs.
3. Finally, a slice type written as `slice<int>` Under the hood, it is a two element struct, with a pointer, and a length field.

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
p[n ...]  is also permissible when indexing a slice or array, for a slice to the end.

The actual way to get a slice of [0] is:
```C5
array<int, 1> y = { 0 };
slice<int> x = y[...];
```


### Destructuring and extending switch
We introduce destructuring syntax for variable assignments and switches.
The syntax broadly mimics ML-family languages, where destructuring appears similar to the designated initalizer syntax.
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

But, the standout use case is in switch. We permit switching on structs as well as numbers.
```C5
switch(get_point()) {
  case {1, int y}: {
    return y;
  }
  case {2, int y}: 
    printf("hello %d", y);
    break;
  }
}
```

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
switch(readFile("foo.txt") {
  case {.kind=RESULT_OK, .data=auto val}:
    data = val;
    break;
  case {.kind=RESULT_ERR, .err=auto e}:
    return e;
}

```

These names that are introduced into the scope are actually aliases for the struct names. 
Thus, things like bitfields should still have the same effect.

### Miscellaneous smaller changes:

* sizeof and typeof require parentheses around their arguments.
* return statements take initializer lists in the grammar, enabling using struct initializers in return position. 

## A closer look at C5 polymorphism

`generic` and `template` may preceede the following:
* struct declarations
* functions
* variable declatations.

For `template` functions and variable declarations, the compiler will generate a family of related values for each instantiation. 
For `generic` functions and variable declarations, the compiler will generate at most one.

Both `generic` and `template` use the same type-parameter-list. This list is enclosed in angle brackets, and must contain one or more parameters. See the example below:
```
generic<type A, size B, constness C>
```
Each parameter must be either `type`, `size`, `constness`.

A `<` following an identifier opens an argument list only if that identifier names a `generic` or `template` entity (or one of the builtins `array` and `slice`) in the current scope; otherwise it is the less-than operator.
Inside an argument list, a `>>` token closes two lists, so `Vec<Vec<int>>` is valid. A `size` argument that contains a top-level `>` or `>>` must be parenthesized, e.g. `array<int, (N > 4 ? 8 : 4)>`.


### Type parameters
Type parameters introduced by a `generic` are incomplete. You can have pointers to them, but you cannot know their size or alignment.
Type parameters introduced by a `template` can have their size and alignment known. It is possible to access their bytes directly, permitting byte-level equality comparisons. 
However, their members are unknown, and duck typing C++ style doesn't work. They cannot be treated as integers, for instance, (even if they are).

### Constness parameters
Constness has two values: `const` and `mut`. Mut is the default. It captures the difference between a type having const and not. It does not capture other modifiers like atomic, volatile, or restrict.

### Size parameters
C5 offers an `size` generic parameter that allows template or generic functions to abstract over array sizes.
In generic functions, this value is totally erased. It is not legal to access N or measure the size of the array.
In template functions, this value is accessible as a constexpr of type size_t. 
Specialization failures (eg via _Static_assert), unlike C++, are real errors, and will be realized at the place of instantiation.
It is never passed as a runtime parameter.

### Example: Collections 

Suppose we have a vector of type T which maintains an allocator.
If we wanted to implement the Collection trait for it, we could do the following:

```c5

// there are no higher kinded types or associated types.
// However, it is relatively simple to list both self and elem in the generics type param list.
generic<type Self, type Elem>
typedef struct {
    size_t (*len)(const Self*);
    Elem*  (*at)(Self*, size_t);
} CollectionVT;

// functions can use Collection while being ignorant about the actual type like:
generic<type C, type E>
E* first(C* c)(using CollectionVT<C, E> coll_vt) { return coll_vt.at(c, 0); }

// We can implement Collection for vec by defining a global variable.
generic<type T, type A>
given const CollectionVT<Vec<T, A>, T> COLL_VEC = { .len = vec_len<T, A>, .at = vec_at<T, A> };

// now if we want to use first for a vec of ints, we can:
int main() {
    Vec<int, LibcAllocator> x = new_vec();
    vec_push(&x, 1);

    // automatically infers type and uses the selected instance
    int* f = first(&x);
}
```


### Controlling C compatibility

Different files have different requirements for classical C compatibility. There are two modes for c5:
1. C compatible
2. C incompatible

In reality, both are slightly incompatible with C. But the former is far more compatible.

In idiomatic C5, the following are banned:
1. VLAs
2. _Generic
3. Normal C array

Also, like in C++, struct names and enum names are accessible without prefix "struct" or "enum".

But, when parsing in C compatible mode, they are kept available. Additionally, in C compatible mode, all keywords are of the form _Template, _Generic, _Let, etc.
You must do:
```C
#include <c5.h>
```
to include the keywords.

When the file being parsed or included ends in .c or .h, it is parsed in C compatible mode. If it ends in .c5 or .h5 it is parsed in C incompatible mode. 