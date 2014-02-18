Gottlob
=======
\textbf{Core Features}. The core logic in Gottlob is a Curry/Sch\"onfinkel version of higher order logic \`a la Takeuti, it is a full generalization of $\systemg$. Church's simple types is used to determine the well-formedness of a formula, the type inference in this case is decidable and we implement a simple version of constraints solving algorithm to check the well-formedness of a formula. Proofs are represented as objects but not functions. The logic includes untyped lambda calculus as its domain of individuals, which is the core for the programs in Gottlob. The treatment of recursion is implicit, namely, we treat global recursive definitions as primitive instead of translating it to the fix point combinator in lambda calculus. We use Scott encoding to support user defined algebraic data. Each data declaration is elaborated into a set of Scott encoded constructors and a inductive set definition. The proof language is in natrual-deduction style, while requires user
to annotate the proof.

\textbf{Proof Pattern and Tactic}. After the second iteration of the implementation, the author realized that the treatment of 
proof as object although simplified the proof checking process, the resulting phenomina
is that the user has to write long proof most of the time even to prove simple lemmas like 
congruence of equality. And long proof greatly affects the readability, while readability
is one of the goals of designing Gottlob. We notice that this issue can be fixed by introducing
user-defined tactics in the proofs. By tactic we mean a meta-program that can take in proofs/formulas/programs as arguments and produce a checkable proof. The idea is that there are many proof patterns that can not be captured only by lemma, but is easily captured by tactic. For example, we know that we can always construct a proof of $t_1 =_{\mathrm{Leibniz}} t_2$ if $t_1$ can be evaluated to $t_2$. However, the notion of ``$t_1$ can be evaluated to $t_2$'' can not captured by the language, so everytime one would need to manually construct a proof of $t_1 = t_2$ for \textit{every} such $t_1$ and $t_2$. It is easy to see that all these proofs are the same except we only 
vary $t_1,t_2$. This proof pattern can be captured by introducing a meta-program that takes
in $t_1, t_2$ as argument and produce a of proof of $t_1 =_{\mathrm{Leibniz}} t_2$. This meta-program
does not need to be typed, because the correctness of its outputs will always be checked
by the proof checker. We are still in the process of implementing the tactic feature.

Since the logic in Gottlob is higher order logic \`a la Takeuti, it can capture some common proof patterns. For example, we know that for \textit{any} formula $F(x)$ with $x$ free in $F$, 
we know that we can always construct a proof of $\forall x.F(x) \to F(x)$. This pattern can
be captured by the proof of $\forall C.\forall x. x \in C \to x \in C$. To obtain a proof of
$\forall x.F_1(x) \to F_1(x)$, one just need to instantiate $C$ with $\iota x.F_1(x)$, then by
comprehension we can get a proof of $\forall x.F_1(x) \to F_1(x)$.

\textbf{About Gottlob Program}. Perhaps the most contraversal design choice of Gottlob is
not to implement a polymorphic type checker for the program fragment. However, we want to
emphasis that we could implement it for the surface language of the program, while after
the elaboration to core calculus, it would becomes untyped. And the execution model and the reasoning of the program occurs at the core level. So a type checker for the program could definitely improve the correctness/logic of the program at the surface language. We consider it is a well-established field and comfortably leave it to the future. As for the execution model, we implement the head reduction we defined in Section \ref{g:pre}. From compilation point of view, there
could be severe performance penalty, we have to again leave this for the future research.

\textbf{Capture-avoiding Substitution and Alpha-Equivalence}. Since our execution model is 
head reduction instead of usual weak head reduction on closed term, we have to handle 
capture-avoiding substitution and alpha-equivalence. We took the simple approach of ``renaming
when necessary'' (originally proposed by Curry citehere) to do the substitution. And when
we need to compare whether two terms are alpha-equivalence, we simply first transform them into
de Bruijn version and then do a syntactic comparison. We have not have much troubles with capture-avoiding substitution and alpha-equivalence. Part of the reason is that the design goal of 
Gottlob is on reasoning about programs instead of being a framework to define logic and to prove
consistency of a logic. 

\textbf{Future Works}. We are currently implementing the tactic feature, and we would like to support Haskell style monadic framework in a untyped setting. Since head reduction is a almost-lazy operational semantics, we can afford definition like $f = \lambda s.\lambda a. t[\mathrm{let} f = f\ (\mathrm{update}\ s) \ \mathrm{in}\ t'[...]]$ $\dagger$, where $s$ represent state, $a$ is an argument for $f$ and ``$\mathrm{update}$'' is some function that take in $s$ and return a new state. $t[...]$ means in side the term $t$. So what we need to do is setting up a monadic syntax and systematically translate that in to the format $\dagger$ above. From a reasoning perspective, this will open the door of reasoning about stateful programs. Last but not least, we also want to implement an interpretor-like environment for user to interact with the proofs or the
programs in Gottlob. 
