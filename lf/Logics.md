## Logic in Coq

### Setoids and Logical Equivalence
- Setoids: a set equipped with an equivalence relation(this relation should be reflexive, symmetric, and transitive).
- When x=y, we can use rewrite to replace one part of a propostion with another.
- The logical equivalence'<->' is similar to '='

### Existential Quantification
- 'exists' we can use tactic 'exists st' to specify one variable with existential quantification to a specfic value('st' for here).

### Programming with Propositions
- in Proof : intros [] = intros H. destruct H.(the hypothesis 'H' should be 'false'(literally))

### Applying Theorems to Arguments
- One feature that distinguished Coq from some other proof assistant is that it **treats proofs as first-class objects**.

### Working with Decidable Propoerties
We have two ways to **expressing logical claims** in Coq:
- with *booleans*(of type `bool`)
- with *propositions*(of type `Prop`)
e.g.
true, false(bool)
True, False(Prop)
