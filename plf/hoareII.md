## Hoare Logic II

> The essential ideas of Hoare-logic proof:
> omitting low-level calculation details -- by "decorating" a program with app

### Decorated Programs

> The beauty of Hoare Logic is that it is structure-guided: the *structue-guided*:
> the structue of proofs exactly follows the structue of programs.

Such a decorated program carries within itself an argument(the assertion) for its own correctness.
e.g.:
program
```Coq
    X := m;
    Z := p;
    while X ≠ 0 do
      Z := Z - 1;
      X := X - 1
    end
```
one possible specification(what it takes and the expected outcome)
```Coq
    {{ True }}
    X := m;
    Z := p;
    while X ≠ 0 do
      Z := Z - 1;
      X := X - 1
    end
    {{ Z = p - m }}
```
decorated version(embodying a proof of this **specification**)
```Coq
    {{ True }} ->>
    {{ m = m }}
      X := m
                         {{ X = m }} ->>
                         {{ X = m ∧ p = p }};
      Z := p;
                         {{ X = m ∧ Z = p }} ->>
                         {{ Z - X = p - m }}
      while X ≠ 0 do
                         {{ Z - X = p - m ∧ X ≠ 0 }} ->>
                         {{ (Z - 1) - (X - 1) = p - m }}
        Z := Z - 1
                         {{ Z - (X - 1) = p - m }};
        X := X - 1
                         {{ Z - X = p - m }}
      end
    {{ Z - X = p - m ∧ ¬(X ≠ 0) }} ->>
    {{ Z = p - m }}
```
Concretely, a decorated program consists of the program's text interleaved with assertions(sometimes multiple assertions seperated by implications).

A decorated program can be viewed as a compact representation of a proof in Hoare Logic:
The assertions surrouding each command specify the Hoare triple to be proved for that part of the program using one of the Hoare Logic rules,
and the structure of the program itself shows how to assemble all these individual steps into a proof for the whole program.

| elements | duty |
| -------- | ---- |
| assertions | specify the Hoare triple to be proved for that part of program |
| the structure of the program itself | shows how to assemble the individual steps in to a proof for the whole |

> Goal : Verify such decorated programs "mostly automatically"

Before we can verify it, we need to be able to fina a proof for a given specification.
Because what we want to prove are Hoare triples, and Hoare triples consist of assertions(want to obtain) and command(what we have now),
so we need to find the right assertions.
The work of finding right assertions can be done almost automatically, except for **finding loop variants**.

#### Example: Swapping
> how to decorate assignment command
Given the following program:
```Coq
       X := X + Y;
       Y := X - Y;
       X := X - Y
```
We can give a proof, in the form of decorations, that this program is correct(i.e., it really swap the X and Y):
```Coq
    (1)    {{ X = m ∧ Y = n }} ->> (* obtain from the precondition of the whole program(specification) *)
    (2)    {{ (X + Y) - ((X + Y) - Y) = n ∧ (X + Y) - Y = m }} (* get form the substitution from (3) *)
             X := X + Y
    (3)                     {{ X - (X - Y) = n ∧ X - Y = m }}; (* get from the substitution from (4) *)
             Y := X - Y
    (4)                     {{ X - Y = n ∧ Y = m }}; (* get from the substitution from (5) *)
             X := X - Y
    (5)    {{ X = n ∧ Y = m }} (* get from the postcondition of the whole program(specification) *)
```
The workflow can be summaried as follows:
1. Begin with the undecorated program.
2. Add the specification: add the precondition and the postcondition for the whole program 
3. From the decorated program we construct, we can find that the main work we do is starting from (5) and proceeding until we get to (2).
   At each step, we obtain the precondition of the assignment from its postcondition by substituting the assigned variable with the right side of the assignment.
4. Finally, we verify the implication of (1) to (2) -- to prove the step from (1) to (2) is a valid use of the law of consequence.

#### Example: Simple Conditionals
> how to decorate conditional command
Here is a simple decorated program using conditionals:
```Coq
      (1)   {{ True }} (* precondition from specification *)
              if X ≤ Y then
      (2)                    {{ True ∧ X ≤ Y }} ->> (* conjoin precondition(1) and guard to obtain this *) 
      (3)                    {{ (Y - X) + X = Y ∨ (Y - X) + Y = X }} (* obtain from substitution of (4) *)
                Z := Y - X
      (4)                    {{ Z + X = Y ∨ Z + Y = X }} (* copy from postcondition(8) *)
              else
      (5)                    {{ True ∧ ~(X ≤ Y) }} ->> (* conjoin precondition(1) and negation of guard to obtain this *)
      (6)                    {{ (X - Y) + X = Y ∨ (X - Y) + Y = X }} (* obtain from substitution of (7) *)
                Z := X - Y
      (7)                    {{ Z + X = Y ∨ Z + Y = X }} (* copy from postcondition (8) *)
              end
      (8)   {{ Z + X = Y ∨ Z + Y = X }}
```
These decorations can be constructed as follows:
1. Start with the precondition(1) and postcondition(8)
2. Following the format dictated by the **hoare_if rule**
   we copy postcondition(8) to (4) and (7) -- because we all konw that the postcondition of a whole conditional command is the postcondition of each of its branches
   we conjoin the precondition(1) with the guard of conditional to obtain (2) -- we konw that we will excute the first branch when the guard holds
   we conjoin the precondition(1) with the negation of the guard of conditional to obtain (5) -- we konw that we will excute the second branch when the negation of guard holds
3. Following the format dictated by the **hoare_asgn**
   we do the substitution(substitute left with right) to obtain (3) and (6)
4. Finally, we verify these two implications: (2) implies (3), (5) implies (6).
Note: both of these implications crucially depend on the ordering of `X` and `Y` obtained from the guard. Because `n - m + m = n` does **not** hold for arbitrary **natural** numbers(e.g., 3-5+5=5)

#### Example: Reduce to Zero
> how to decorate while command
Here is a `while` loop that is so simple that `True` suffices as a loop invariant.
```Coq
        (1)    {{ True }} (* the precondition(also the invariant for the following while loop) from specification *)
                 while X ≠ 0 do
        (2)                  {{ True ∧ X ≠ 0 }} ->> (* conjoin invariant with the guard of while loop *)
        (3)                  {{ True }} (* obtain from substitution of (4) *)
                   X := X - 1
        (4)                  {{ True }} (* copy from (1) ???point of this decoration??? *)
                 end
        (5)    {{ True ∧ ~(X ≠ 0) }} ->> (* conjoin the invariant and the negation of the guard of the while loop *)
        (6)    {{ X = 0 }} (* the postcondition from specification *)
```
The decorations can be constructed as follows:
1. Start with the outer precondition(1) and postcondition(6)
2. Following the format dictated by the **hoare_while rule**
   we copy (1) to (4) -- based on the **hoare_while rule**: the invariant will not change after the execution of the body of while loop
   we conjoin (1) with the guard to obtain (2) -- based on the **hoare_while rule**: if the guard holds, then the body will be executed and we still need the invariant Why???????????????????????
   we conjoin (1) with the negation of the guard to obtain (5) -- when the guard doesn't hold no longer, then we can reach the place after the `end` notation
3. Because the final postcondition(6) doesn't syntactically match (5), so we add an implication between them
4. Following the format dictated by the **hoare_asgn rule**
   we do the substitution for (4) to obtain (3)
5. We add the implication between (5) and (6)
6. Finally we check the implications do hold; both are trivial.

#### Example: Division
> how to decorate more complex while loop
The following Imp program calculated the integer quotient and remainder of parameters `m` and `n`.
```Coq
       X := m;
       Y := 0;
       while n <= X do
         X := X - n;
         Y := Y + 1
       end;
```
In order to give a specification to this program we need to remember that dividing `m` by `n`
produces a remainder `X` and a quotient `Y` such that `n * Y + X = m /\ X < n`.

And we can find the invariant easily: `n * Y + X = m`, we can use this to decorate the program.
```Coq
      (1)  {{ True }} ->> (* precondition from specification *)
      (2)  {{ n × 0 + m = m }} (* substitution from (3) *)
             X := m;
      (3)                     {{ n × 0 + X = m }} (* substitution from (4) *)
             Y := 0;
      (4)                     {{ n × Y + X = m }} (* the invariant we find above *)
             while n ≤ X do
      (5)                     {{ n × Y + X = m ∧ n ≤ X }} ->> (* if we want enter this body, we should ensure that the guard holds *)
      (6)                     {{ n × (Y + 1) + (X - n) = m }} (* substitution from (7) *)
               X := X - n;
      (7)                     {{ n × (Y + 1) + X = m }} (* substitution from (8) *)
               Y := Y + 1
      (8)                     {{ n × Y + X = m }} (* copy from (4) the invariant doesn't change after every execution of loop body *)
             end
      (9)  {{ n × Y + X = m ∧ ¬(n ≤ X) }} ->> (* if we want to get out of the loop body, we need to ensure that the negation of loop guard holds and conjoin it with invariant *)
     (10)  {{ n × Y + X = m ∧ X < n }} (* the postcondition from specification *)
```

The construction of this decoration is same as the examples before.

#### From Decorated Programs to Formal Proofs
Note that we do *not* unfold the definition of hoare_triple anywhere in this proof:
the point of the game is to use the Hoare rules as a self-contained logic for reasoning about proragms.


### Formal Decorated Programs
Our informal conventions for decorated programs amount to a way of "displaying" Hoare triples,
in which commands are annotated with enough embedded assertions that
checking the valiadity of a triple is reduced to simple logical and algebraic caculations showing that some assertions imply others.

#### Syntax
The first thing we need to do is to formalize a variant of the syntax of commands that includes embedded assertions --  decorations.
We call the new commands `decorated commands`, or `dcoms`.

Where to put assertions in the definition of `dcom`?

In general, we omit the preconditions whenever possible, trying to embed just the postcondition.
Concretely, we decorate programs as follows...
- skip
    skip {{Q}}
  on the assumption that the precondition will be provided by the context.
- sequences `d1; d2`
  need no decorations. Why? 
  - the precondition of sequence will be provided by the context.
  - the postcondition of sequence will be provided by the postcondition of its subcommand `d2`.
- assignment `X := a`
  is decorated only with its postcondition
    X := a {{Q}}
- conditional `if b then d1 else d2`
  is decorated
