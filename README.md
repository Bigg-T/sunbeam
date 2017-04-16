# sunbeam

- **S**tructs
- **U**nite
- **N**ums,
- **B**ools, and
- **E**xprs, can
- **A**ccess and
- **M**odify

![snake](https://c2.staticflickr.com/4/3934/15470067401_ae2b610124_b.jpg)

---

## New Types
```
type prim1 =
  ...
  | StructHuh of string
```

```
type 'a dstruct =
  | DStruct of string * (string * 'a) list * 'a

type 'a program =
  | Program of 'a dstruct list * 'a expr * 'a
```

```
and 'a expr =
  ...
  | EStructInst of string * 'a expr list * 'a
  | EStructGet of string * string * 'a expr * 'a
  | EStructSet of string * string * 'a expr * 'a expr * 'a
```

```
type 'a aprogram =
  | AProgram of 'a dstruct list * 'a aexpr * 'a
```

```
and 'a cexpr =
  ...
  | CStructInst of string * 'a immexpr list * 'a
  | CStructGet of string * string * 'a immexpr * 'a
  | CStructSet of string * string * 'a immexpr * 'a immexpr * 'a
```

#### Design Decision
We require all struct definitions to be defined in a separate data definition.
We do this because we believe that it improves the overall programming experience --
all data definitions are easily found at the beginning of the program, they cannot be
redefined, and this separation tends to be the structure of larger programs anyway.

## New Parse Rules

| Feature | BSL Racket  | Sunbeam  |
|---|---|---|
| 1. define  | `(define-struct document (wordcount rating))`  | `(define-struct document (wordcount, rating))`  |
| 2. inst  | `(define doc1 (make-struct (500, 98)))`  | `let doc1 = (make-struct (500, 98))`  |
| 3. huh  | `(document? doc1)`  | `(document? doc1)`  |
| 4. get  | `(document-wordcount doc1)`  | `(document-wordcount doc1)`  |
| 5. set  | `(set-document-wordcount! doc1 100)` | `(document-wordcount doc1) := 100` |

#### Syntax Design Decisions
For the most part, we chose to make our language's syntax mimic BSL Racket's struct syntax.
The main differences are in instantiation and mutation. With instantiation, we leverage our
`let` syntax, as we don't have the equivalent of a Racket `define`. Also, BSL Racket allows
users to define structs with no fields, but like with tuples, our parser cannot do this without
being ambiguous. As for mutation, we didn't want to use the `!` as we are already using that to
indicate binary `not`, not mutation, and we are using the `:=` to mimic the choice made for
modifying tuples.

New tokens:
```
| "define-struct" { DEFSTRUCT }
| "make" { MAKE }
| "?" { QUESTION }
```

```
simple_expr :
  ...
  | LPAREN ID MINUS ID expr RPAREN { EStructGet($2, $4, $5, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | LPAREN ID MINUS ID expr RPAREN GETS expr { EStructSet($2, $4, $5, $8, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

expr :
  ...
  | MAKE MINUS ID LPAREN exprs RPAREN { EStructInst($3, $5, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  ...

dstruct :
  | DEFSTRUCT ID LPAREN ids RPAREN { DStruct($2, $4, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }

dstructs :
  | dstruct { [$1] }
  | dstruct dstructs { $1::$2 }

program :
  | dstructs expr EOF { Program($1, $2, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
  | expr EOF { Program([], $1, (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())) }
```


## Compile

First we create our struct environment (`struct_env`) using the struct definitions in
the `Program` by calling `make_struct_env`. This creates an entry for each struct definition
in an association list that records the name of the struct, a unique tag, and the field names.
We pass that `struct_env` to the compile functions.

The given document instance looks like this on our heap:

```
make-struct document (wordcount, rating, recommended)
let doc1 = make-document (500, 100, true) in doc1
```

| unique tuple tag | # of fields | field1 | field2 | field3 | padding |
|---|---|---|---|---|---|
| `0x02` | `0x06` | `0x3E8` | `0xC8` | `0xFFFFFFFF` | `0x0` |

We use the unique tuple tag field to test if a certain value is a certain type of struct,
as in `document?`. As long as the value is a struct, we look up "document" in the `struct_env`,
get its tuple tag, and compare it with the first word of the struct's heap space.


## Wellformedness

- `DuplicateStructDef`
- `UnboundStructName`
- `UnboundFieldName`
- `MismatchFieldArity`

## Optimize

We can remove struct definitions that are never used in the program during DAE,
so we added this in `dae_dstruct`. `CStructInst`, `CStructGet`, and `CStructSet`
can have their respective `immexpr`s optimized.

## Difficulties

- the design process
- bugs inherited from our previous compilers (like the purity analysis...)
