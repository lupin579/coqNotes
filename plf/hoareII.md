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

