## Types

> We'll introduce the basic ideas of *types* and *typing rules* and the fundamental theorems about type systems: *type preservation* and *progress*

### Typed Arithmetic Expressions

#### Syntax

#### Operational Semantics

Notice that the `step` relation doesn't care about whether the expression being stepped makes global sense --
it just checks that the operation in the next reduction step is being applied to the right kinds of operands.
e.g.:
the term `<{succ true}>` cannot take a step
the almost obviously nonsensical term
    <{ succ (if true then true else true) }>
can take a step.

#### Normal Forms and Values

The first interesting thing to notice about the `step` relation is that
the strong progress theorem fails here.

That is, there are terms that are normal forms(can't take a step) but not values(i.e., there are normal forms that are not included in the possible results of reduction).
Such terms are called `stuck`.

#### Typing

We can easily exclude the nonsensical stuck terms by defining  a typing relaition that relates terms to the types(either numeric or boolean) of their final results.
```Coq
Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.
```

Informal notation:
 `|-- t \in T` (pronounced "`t` has type `T`", `|--` is called `turnstile`)

Notice:
The typing relation is a conservative(or static) approximation:
It doesn't consider what happens when the term is reduced -- in particular, it doesn't calculate the type of its normal form.

There are two critical properties of typing relation:
- progress
- type preservation

#### Progress

Definition:
The well-typed normal forms are never stuck, or conversely,
if a term is well-typed, then either it is a value or it can take at least one step(the additional possibility can be loop(forever)).

Compare this theorem with the strong progress theorem where all normal forms are values.
Notice: `stuck` is also a type normal form, but it is ill-typed.

#### Type Preservation

Definition: When well-typed term takes a step, the result is a well-typed term(of the same type).

#### Type Soundess
Putting progress and preservation together, we see that **a well-typed term can never reach a stuck state**.
```Coq
Definition multistep := (multi step)
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundess : forall t t' T,
  |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
```
