## Inductively Defined Propositions

**Transitive closure(of a relation R)**: the smallest relation that contains R and that is transitive.

```Coq
Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS (n : nat)(H : ev n) : ev (S (S n)).
```

**evidence constructors(like the ev_0,ev_SS above)**: we can think of these as the name of the evidence(the propostions) on the right of colons,
or primitive evidence of something.

```Coq
Inductively le : nat -> nat -> Prop :=
    | le_n (n : nat) : le n n
    | le_S (n m : nat) : le n m -> le n (S m)
```
from the annotaition([nat -> nat -> Prop]) of the definition above, we can find this is a property(a definition results in a Prop).

```Coq
Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. ∃ n'. split. reflexivity. apply E'.
Qed.
```
we can destruct the inductively defined proposition(like the [ev n](not an only [ev]) above)

what does the inversion do underlyingly?
```Coq
Theorem ev_inversion : ∀ (n : nat),
    ev n →
    (n = 0) ∨ (∃ n', n = S (S n') ∧ ev n').
Proof.
  intros n E. destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. ∃ n'. split. reflexivity. apply E'.
Qed.
```
the `inversion in H.` is just the abbrievation of `ev_inversion`  above.

watch out the difference of a proposition applied to a [hypothesis] and a [target].
