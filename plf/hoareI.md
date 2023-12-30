## HOARE LOGIC I

Hoare Logic(Floyd-Hoare Logic):
is a reasoning system in which each of the syntactic contructs of Imp is equipped with a generic "proof rule" that can be used to reason compositionally
about the correctness of programs involving this construct.

We proved a number of metatheoretic properties -- "meta" in the sense that
they are properties of the language as a whole, rather than particular programs
in the language. These included:
- **determinism** of evaluation
- equivalence of some **different ways of writing down the definitions**(e.g., functional and relational definitions of arithmetic expression evaluation)
- **guaranteed termination** of certain classes of programs
- correctness(in the sense of **preserving meaning**) of a number of useful program transformations
- **behavioral equivalence** of programs

Hoare Logic combines two ideas:
- a natural way of writing down specifications of programs,
- a structured proof technique for proving that programs are correct with respect to such specifications
(Ps : the structured we mean that the structure of proofs directly mirrors the structure of the programs that they are about)

### Assertions
An assertion is a logical claim about the state of program's memory -- formally, a **property of states**.
```Coq
Definiton Assertion := state -> Prop.
```
e.g.
- fun st => st X = 3 holds for state st in which value of X is 3(st X = 3 is the propostion, what we need to do is to prove there is a witness(value) of this propostion(this type)),
- fun st => True     holds for all states (True is the propostion, and we konw that there is always a value(witness) in this type(propostion), so it holds for all states)
- fun st => False    holds for no states (False is the propostion, and we konw that there is no value(witness) in this type(propostion), so it holds for no state)
--------------------------------------------------------
the practical perspective of eg1:
we suppose that
P := fun st => st X = 3,
st1 = {X !-> n; ...}(n is an arbitrary number)
execution:
   P st1
-> (fun st => st X = 3) {X !-> n; ...}
-> ({X !-> n; ...} X) = 3
-> n = 3 (:Prop)
--------------------------------------------------------
For convenience, instead of writing
    fun st => st X = m
we'll write just
    X = m.
The reason why we can write like this is:
1. every single assertion that we ever write is going to begin with fun st =>
2. this state st is the only one that we ever use to look up variables in assertions(**we will never need to talk about two different memory states at the same time**)

In informal assertions, capital letters like X, Y and Z are Imp variables,
while lower letters like x, y, m, and n are ordinary Coq variables(of type nat)

The implication of assertions:
P ->> Q (P implies Q, whenever P holds in some state st, Q also holds in the same states.)
```Coq
Definition assert_implies (P Q : Assertion) : Prop :=
    forall st, P st -> Q st.
Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.(* this annotation tells Coq this notation is not global but is intended to be used in particular contexts *)
Open Scope hoare_spec_scope.(* this line tells Coq this file is one such context *)
```

The iff variant of implicaiton between assertions:
p <<->> Q = (P ->> Q) /\ (Q ->> P) : hoare_spec_scope

### Hoare Triples, Informally
- Definition:
  A Hoare Triple is a claim about the state before and after executing A command.
- Standard Notion:
  {P} c {Q} (`P` is called the precondition of the triple, and `Q` is the postcondition)
  meaning:
  - If command c begins execution in a state satisfying assertion `P`,
  - and id c eventually **terminates** in some final state,
  - then that final state will satisfy the assertion `Q`.
- To avoid the symbol confilct, we use {{P}} instead of {P}

e.g.
- {{X = 0}} X := X + 1 {{X = 1}} is a valid Hoare triple
- forall m, {{X = m}} X := X + 1 {{X = m + 1}} is a propostion stating that the Hoare triple {{X=m}} X := X + 1 {{X=m+1}} is valid for any choice of m

### Hoare Triples, Formally
the formal definition of `{{P}} c {{Q}}`
```Coq
Definition hoare_triple
           (P : Assertion) (C : com) (Q : Assertion) : Prop :=
    forall st st',
            st =[c]=> st' ->
            P st ->
            Q st'.
```

### Proof Rules
- The goal of Hoare logic:
  provide a compositional method for proving the validity of specific Hoare triples(i.e., we want the structure of a program's correctness proof to mirror the structure of the program itself)
- Target of proof rules:
  we'll introduce a rule for reasoning about each of the different syntactic forms of commands in Imp, plus a couple of "structual" rules for gluing things together.
  **we'll then be able to prove programs correct using these proof rules, without ever unfolding the definition of `hoare_triple`**.

#### Skip
Since `skip` doesn't change the state, it preserves any assertion `P`:
----------------- (hoare_skip)
{{P}} skip {{P}}
Theorem hoare_skip : forall P,
    {{P}} skip {{P}}.

#### Sequencing
{{P}} c1 {{Q}}
{{Q}} c2 {{R}}
---------------- (hoare_seq)
{{P}} c1;c2 {{R}}

Theorem hoare_seq : forall P Q R c1 c2,
{{Q}} c1 {{R}} ->
{{P}} c2 {{Q}} ->
{{P}} c1; c2 {{R}}.

Note that: in the formal rule hoare_seq, the premises are given backwards order.
This matches the natural flow of information in many situations where we'll use the rule,
since the natural way to construct a **Hoare-logic proof** is to begin at the end of the program(with the final postcondition)
and push postcondition backwards through commands until we reach the beginnig.

#### Assignment(most fundamental)
**{{Q[X |-> a]}} X := a {{Q}}**

The following shows us how this proof rule works:

The postcondition could be some arbitrary assertion Q,
and the right-hand side of the assignment could be some arbitrary arithmetic expression a:
    {{???}} X := a {{Q}}
The precondition(the `???`) would then be `Q`, but with any occurences of `X` in it replaced by `a`.
    Q[X |-> a](means Q where a is substituted in place of X)
So the Hoare logic rule for assignment is:
    {{Q[X |-> a]}} X := a {{Q}}
To formalize the rule, we must first formalize the idea of 
    "substituting an expression for an Imp variable in an assertion"
which we refer to as assertion substitution, or `assn_sub`. That is,
intuitively, given
- an assertion `P`
- a variable `X`
- an arithmetic expression `a`
we want to derive another assertion `P'` that just the same as `P` except that `P'` should mention `a` where `P` mentions `X`.
We can acheive this by evaluating `P` in an updated state(the formal definition):
```Coq
Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).
```
Demonstration:
We suppose that `P` is `fun st => st X = 3`, `st'` is `{X !-> n}`
If we just use `P st'`, then what we'll get is the propostion `n = 3`;
but if we first use `P' = assn_sub X (X + 1) P`, then `P' st'`,
the structure of interior is
P' =
-> fun st => (fun st => st X = 3) {X !-> aeval st (X + 1); st}(* a = (AId) X + 1 *)
-> fun st => ({X !-> aeval st (X + 1); st} X) = 3
-> fun st => aeval st (X + 1) = 3
-> fun st => aeval st X = 2
-> fun st => st X = 2 (aeval st X => st X, because X is a variable)

We'll get the propostion `P' = fun st => st X = 2`
So the Hoare Triple is
    {{P'}} X = X + 1 {{P}}
    {{X = 2}} X = X + 1 {{X = 3}}

#### Consequence
Now we are going to apply the polymorphism(like implementation and interface in Java) in other languages into our Hoare rules
For instance,
    {{(X = 3)[X |-> 3]}} X := 3 {{X = 3}}
follows directly from the assignment rule, but
    {{True}} X := 3 {{X = 3}}
does not. The `true` and the `(X = 3)[X |-> 3]` are syntactically different but logically equivalent.
So we can capture this observation with the following rule:
    {{P'}} c {{Q}}
      P <<->> P'
    -------------- (hoare_consequence_pre_equiv)
    {{P}} c {{Q}}
Taking this line of thought a bit further, we can see that
1. strengthening the precondition or
2. weakening the postcondition
always produces another valid triple.
    {{P'}} c {{Q}}
        P ->> P'
    -------------- (hoare_consequence_pre)
    {{P}} c {{Q}}

    {{P}} c {{Q'}}
       Q' ->> Q
    -------------- (hoare_consequence_post)
    {{P}} c {{Q}}

Here are the formal versions:
```Coq
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
```
Finally, we can combine the rules above to produce a rule that allows us to vary both the precondition and the postcondition.
    {{P'}} c {{Q'}}
        P ->> P'
        Q' ->> Q
    --------------- (hoarr_consequence)
     {{P}} c {{Q}}
formal version:
```Coq
Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
```
#### Automation
Goal:
We hope that in the assistance of automation,
1. we can just focus on what Hoare rules need to be used and
2. leave the remaining low-level details up to Coq to figure it out.

Recall(maybe)
1. the `auto` tactic can be told to unfold definitions as part of its proof search.
Let's give that hint for the definitions and coercions we're using:
```Coq
Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.
```
2. the `auto` will search for a proof involving `intros` and `apply`. By default, the theorems that it will aplly include any of the local hypotheses, as well as theorems in a core database.
```Coq
Theorem hoare_consequence_pre' : ∀ (P P' Q : Assertion) c,
  {{P'}} c {{Q}} →
  P ->> P' →
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.
```
The proof above seems to be able to be replaced with auto.
```Coq
Theorem hoare_consequence_pre' : ∀ (P P' Q : Assertion) c,
  {{P'}} c {{Q}} →
  P ->> P' →
  {{P}} c {{Q}}.
Proof.
  auto. (* no progress *)
Abort.
```
The problem is `apply HHoare with...` part of the proof. Coq isn't able to figure out how to instantiate `st` without some help from us.
Recall again, there are versions of many tactics(e.g.: eapply, e..) that will use exsitential variables to make progress even when regular versions of those tactics would get stuck.

For example, the `eapply` tactic will introduce an existential variable `?st` as a placeholder(will be placed in the shelved page) for `st`,
and `eassumption` will instantiate `?st` with st when it discovers `st` in assumption `Heval`.
So, essentially the use of `eapply` is to tell Coq, "Be patient: The missing part is going to be filled in later in the proof"
```Coq
Theorem hoare_consequence_pre''' : ∀ (P P' Q : Assertion) c,
  {{P'}} c {{Q}} →
  P ->> P' →
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  eapply Hhoare.
  - eassumption.
  - apply Himp. assumption.
Qed.
```
The `eauto` will use `eapply` as part of its proof search. So, the entire proof can actually be done in just one line.
```Coq
Theorem hoare_consequence_pre'''' : ∀ (P P' Q : Assertion) c,
  {{P'}} c {{Q}} →
  P ->> P' →
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.
```

#### Sequencing + Assignment
e.g.:
Notice the order of proving the premises
```Coq
Example hoare_asgn_example3 : ∀ (a:aexp) (n:nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* **right** part of seq *)
    apply hoare_skip.
  - (* **left** part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assn_auto.
Qed.
```
Informally, a nice way of displaying a proof using the sequencing rule is as a "decorated program" where the intermediate assertion `Q` is written between `c1` and `c2`:
{{ a = n }}
   X := a
            {{ X = n }}; <-----decoration for `Q`
   skip
{{ X = n}} -----------------------------------------------TODO-------------------------------------------------

#### Conditionals

First attempt:

        {{P}} c1 {{Q}}
        {{P}} c2 {{Q}}
--------------------------------
{{P}} if b then c1 else c2 {{Q}}

We can find that we missing some something, we forget to add the state of guard(`b`) to it.

So the modified one is
        {{P /\  b}} c1 {{Q}}
        {{P /\ ~b}} c2 {{Q}}
----------------------------------- (hoare_if)
{{P}} if b then c1 else c2 end {{Q}}

If we want to formalize this rule, we need to do some preliminary work:
 lift `b` to type `assertion`
Because the `P` on the left-hand side of the conjuction has type `assertion`
So we'll write `bassn b` for the assertion "the boolean expression `b` evaluates to `true`(in the given state)."

```Coq
Definition bassn b : Assertion :=
  fun st => (beval st b = true).
Coercion bassn : bexp >-> Assertion.
Arguments bassn /.
```
A useful fact about `bassn`:
```Coq
Lemma bexp_eval_false : ∀ b st,
  beval st b = false -> ~ ((bassn b) st).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false : core.
```

Now we can formalize the Hoare proof rule for conditionals and prove it correct.

```Coq
Theorem hoare_if : ∀ P Q (b:bexp) c1 c2,
  {{ P /\   b}} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.

(* following is the unwrapped version *)
Theorem hoare_if : ∀ P Q b c1 c2,
  {{fun st ⇒ P st ∧ bassn b st}} c1 {{Q}} →
  {{fun st ⇒ P st ∧ ¬(bassn b st)}} c2 {{Q}} →
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.
```

#### While Loops

The Hoare rule for `while` is based on the idea of an invariant.
> invariant: an assertion whose truth is guaranteed before and after executing a command.
An assertion `P` is an invariant of `c` if
    {{P}} c {{P}}
holds. **Note that** in the middle of executing `c`, the invariant might temporarily become false, but by the end of c, it must be restored. 


