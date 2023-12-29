## Simple Imperative Programs

### Coq Automation
Coq's automation is a powerful tool, but it scale up our efforts to more complex definitions
and more interesting properties without becoming overwhelmed by boring,repetitive, low-level details.

1. Try
`try T` 
if `T` fails -> `try T` successfully does nothing at all(rather than failing)
if `T` success -> just do the things as `T` does

2. ;
`T1; T2; T3;..`(Simple Form)
`T1; [T2 | T3 | ..]`(General Form)
first performs `T1`, then performs `T2` on all results of `T1`
usually be used as `induction ..; try ..`

3. repeat
`repeat T`
**repeat never fails**: if `T` doesn't apply on the original goal -> repeat succeeds without changing the goal at all
**no upper bound**: if `T` always succeeds(and **make progress**), then repeat `T` will loop **forever**

e.g. (for no upper bound)
```Coq
Theorem repeat_loop : forall (m n : nat),
 m + n = n + m.
Proof.
  intros m n.
  repeat rewrite Nat.add_comm.(* the commutation of addition fot nat *)
Admitted.
```
Ps: 
- This non-terminate perform is only in the *proof*, that means:
- Coq's term language Gallina is guaranteed to terminate, but *tactic* evaluation is not.
- So if the construction process diverges(i.e. it doesn't terminate), 
  that just means we just failed to constructing proofs, not that we have constructed a bad proof.

### Defining New Tactics
Coq also provides facilities for "programming" in tactic scripts.

- Ltac(keyword or idiom)
    - Defines "shorthand tactics" that bundle several tactics into a single command.
    - Includes syntactic pattern_matching on the goal and context.
    - Analogous ways of defining new tactics: `Tactic Notation`, a low-level API
e.g.
```Coq
Ltac invert H :=
  inversion H; subst; clear H.
```

- lia(Tactic)(need `Import Lia` at the top of this file)
If the goal is a universally quantified procedure made out of
1. numeric constants, + and S, - and pred, * by cosntants
2. = and <>, ordering(<,>,<=,>=)
3. logical connectives `and`, `or`, `~`, `->`
then invoking `lia` will ether solve the goal or fail(meaning that the goal is actually false)(If the goal is not of this form, `lia` will also fail,)
```Coq
Example silly_presburger_example : ∀ m n o p,
  m + n ≤ n + o ∧ o + 3 = p + 3 →
  m ≤ p.
Proof.
  intros. lia.
Qed.
Example add_comm__lia : ∀ m n,
    m + n = n + m.
Proof.
  intros. lia.
Qed.
Example add_assoc__lia : ∀ m n p,
    m + (n + p) = m + n + p.
Proof.
  intros. lia.
Qed.
```

- clear H : Delete hypothsis H from the context
- subst x : Given a variable x 
  1. find an assumption x=e or e=x in the context,
  2. replace x with e throughout the **context and current goal**,
  3. and clear the assumption.
- subst: Substitute away all asssumptions of the form x=e or e=x(where x is a variable)
- assumption: Try to find a hypothesis `H` in the context(the hypotheses) that **exactly matches the goal**; If one is found, `solve the goal`.
- contradiction: Try to find a hypothesis `H` in the context that is **logically equivalent to `False`**. If one is found, `solve the goal`.
- constructor: Try to find a constructor `c` in the context that **can be applied to solve the current goal**. If one is found, behave like `apply c`.

### Computational(Functional) vs. Relational Definitions

For the definition of evaluation for arithmetic and boolean expressions

Arithmetic operation:
```coq
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp). (* <--- NEW *)
```

Relational:
```coq
Reserved Notation "e '==>' n" (at level 90, left associativity).
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus E_AMult 
      ...
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) : (* <--- NEW *)
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) -> n3
```

For the relational evaluation definition above if we wanna use computational evaluation to define it,
we need to concentrate on how distinguish the cases that the divisor is zero or not(there is no `when` keyword in Coq like ocaml?)

------------------------------------------------

The following is another example that can be difined in relational evaluation but can't in computational ones. 
```coq
Reserved Notation "e '==>' n" (at level 90, left associativity).
Inductive aexp : Type :=
  | AAny (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
```

```coq
Inductive aevalR : aexp → nat → Prop :=
  | E_Any (n : nat) :
      AAny ==> n (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) → (a2 ==> n2) → (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) → (a2 ==> n2) → (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) → (a2 ==> n2) → (AMult a1 a2) ==> (n1 × n2)

where "a '==>' n" := (aevalR a n) : type_scope.
```

In the examples we've just seen, relational definitions turned out to be more useful than functional ones.
For situations like this, where
- the thing being defined is not easy to express as a function
- indeed where it is not a function, there is no real choice.

What about both styles are workable?(Fixpoint(functional) and Inductive(relational))
The superiority for each definition style:

relational definitions:
- more elegant and easy to understand
- Coq automatically generates useful inversion and induction principles from Inductive definitions but not from Fixpoint

functional definitions:
- Functions are automatically deterministic and total; for a relational definition, we have to *prove* these properties explicitly if we need them
- With functions we can also take advantage of Coq's computation machanism to simplify expressions during proofs
- **Futhermore,** functions can be directly extracted  from Gallina to excutable code in OCaml or Haskell 
Indeed, in large Coq developments it is common to see a definition given in both functional and relational styles,
plus a lemma stating that the two coincide, allowing further proofs to switch from one point of view to the other at will.

The States(the **Map**)
### Commands
The *Determinism of Evaluation*'s  partial function is what? read the Map chapter
