## The Curry-Howard Correspondence

Well! The essence of proof is the procedure of finding an evidence of a specific propositions.
From the prespective of programming, what we do is building a tree of evidence(which can be thought of as a data structure).

If the proposition is an implication like `A -> B`, then its proof will be an evidence transformer:
a recipe for converting evidence for A into evidence for B.
**So at a fundamental level, proofs are simply programs that manipulate evidence.**

Propositions are **types**!

e.g.
```Coq
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S(S n)).
```
At here, for the `:`, we can say "is a proof of" instead of "has type".
For example, for the second line, we can say ev_0 'is a proof of' ev 0, instead of ev_0 has type ev 0.

### Proof Scripts
For a proof of a former lemma.
```Coq
Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.(this line is the *proof script*)

Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0) *) (this line and the next line are the same thing, the *proof object*)
Check (ev_SS 2 (ev_SS 0 ev_0)) : ev 4.
```
Proof script And Proof object:
- Proof script is the recipe of finding the data structure(the evidence)
- Proof object is that data structure(the evidence)
- i.e. proof script is the script to build the proof object

Proof Scripts
From the conception of proof script and proof object, we konw that the tactics between `Proof` and `Qed` tell Coq how to build up a term whose type is the proposition being proved.
```Coq
Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.
```
We can use `Show Proof` command to display the current state of the proof tree(the current state of the proof object) at any points as above.
At any given moment, we can notice that Coq construct a term with a `?Goal`(the "hole")),and Coq konws what type of evidence is needed to fill this hole.
Each hole corresponds to a subgoal(we can see its proposition(the type) on the right upper tab).
When there are no more subgoals, this proof is finished. 
And at this point, the proof object(the evidence) we've built is stored in the global context bound with the name given in the `Theorem` command.

Fromt above, we can find the essential content(the essence) of proof is finding the a proof object(a evidence) with the type of this proposition.
So essentially, what we need to do is build an evidence for the type of a specific proposition.
That means we can directly build evidence(using `Definition` rather than `Theorem` to introduce a global name for this evidence) instead of using proof script(although it's very convenient).
```Coq
Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).
```

### Quantifiers, Implications, Functions

