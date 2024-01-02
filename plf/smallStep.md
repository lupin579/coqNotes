## SMALL-STEP

> Goal: replace the "big-step" eval relation with a "small-step" relation

We have defined the big-step semantics evaluator(the natural semantics),
> why we still need to define the small-step semantics?
There are something big-step semantcis doesn't do well.
E.g.:
- it doesn't give us a natural way of talking about concurrent programming languages
- a command might fail to map a starting state to any ending state for two reasons:
  - nontermination
  - some operations make no sense(erroneous "stuck states")
  and we want to distinguish the first reason from the second one

### Toy Language

Given a toy language with just `Contant` and `Plus` two constructors.
```Coq
Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
```
Here is a standard evaluator for this language(written in big-step style)
```Coq
Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.
```
Here is the same evaluator, but formulated as an inductively defined relation.
We use the notation `t ==> n` for "t evaluates to n"

             --------- (E_Const)
             C n ==> n

             t1 ==> v1
             t2 ==> v2
         -------------------- (E_Plus)
         P t1 t2 ==> v1 + v2
```Coq
Reserved Notation " t '==>' n " (at level 50, left associativity).
Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 v1 v2,
      t1 ==> v1 ->
      t2 ==> v2 ->
      P t1 t2 ==> (v1 + v2)

where " t '==>' n " := (eval t n).
```

The following is the corresponding *small-step* evaluation relation.

         --------------------------- (ST_PlusConstConst)
         P (C v1) (C v2) --> v1 + v2

                  t1 --> t1'
            -------------------- (ST_Plus1)
            P t1 t2 --> P t1' t2

                     t2 --> t2'
            ---------------------------- (ST_Plus2)
            P (C v1) t2 --> P (C v1) t2'
```Coq
Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm → tm → Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      t2 --> t2' ->
      P (C v1) t2 --> P (C v1) t2'

  where " t '-->' t' " := (step t t').
```

### Relations

We will be working with several different single-step relaions, so
> Goal : state a few definitions and theorems about relations in general.


