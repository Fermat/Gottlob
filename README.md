Gottlob
=======
**Core Features**. The core logic in Gottlob is a Curry/Schönfinkel version of higher order logic à la Takeuti, it is a full generalization of **G**. Church's simple types is used to determine the well-formedness of a formula, the type inference in this case is decidable and we implement a simple version of constraints solving algorithm to check the well-formedness of a formula. Proofs are represented as objects but not functions. The logic includes untyped lambda calculus as its domain of individuals, which is the core for the programs in Gottlob. The treatment of recursion is implicit, namely, we treat global recursive definitions as primitive instead of translating it to the fix point combinator in lambda calculus. We use Scott encoding to support user defined algebraic data. Each data declaration is elaborated into a set of Scott encoded constructors and a inductive set definition. The proof language is in natrual-deduction style, while requires user
to annotate the proof.


**About Gottlob Program**. Perhaps the most contraversal design choice of Gottlob is
not to implement a polymorphic type checker for the program fragment. However, we want to
emphasis that we could implement it for the surface language of the program, while after
the elaboration to core calculus, it would becomes untyped. And the execution model and the reasoning of the program occurs at the core level. So a type checker for the program could definitely improve the correctness/logic of the program at the surface language. We consider it is a well-established field and comfortably leave it to the future. As for the execution model, we implement the head reduction. From compilation point of view, there
could be severe performance penalty, we have to again leave this for the future research.



