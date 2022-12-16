\documentclass{article}

% workaround, see https://github.com/kosmikus/lhs2tex/issues/82
\let\Bbbk\undefined

%include agda.fmt
%include custom.fmt

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{stmaryrd}
\usepackage{listings}
\usepackage[pdftex]{xcolor}
\usepackage{xspace}
\usepackage{xcolor}
\usepackage{hyperref}
\usepackage{colortbl}
\usepackage{todonotes}

\newcommand{\Draft}[1]{}
% \newcommand{\Fixme}[1]{}
% \newcommand{\Draft}[1]{\todo[inline,backgroundcolor=gray!30]{#1}}
\newcommand{\Fixme}[1]{\todo[color=orange!30]{#1}}

\newcommand{\Let}[1]{\textbf{let } #1 = }
\newcommand{\LetB}{\textbf{let }} % using de Bruijn indices
\newcommand{\In}{\textbf{ in }}
\newcommand{\DeBruijn}[1]{\langle #1 \rangle}

\newcommand{\X}{\cellcolor{gray}}
\newcolumntype{L}{>{\centering\arraybackslash}X}
\newcommand{\Week}[1]{\tiny #1}

\title{Thesis Proposal: Analysis and Transformation of Intrinsically Typed Syntax}

\author{Matthias Heinzel}

\date{\today}

\begin{document}

\maketitle

\tableofcontents
\pagebreak


\section{Introduction}

\Draft{What is the problem? Illustrate with an example.}
\Fixme{Mostly copied from report, revisit!}

When writing a compiler for a programming language,
an important consideration is the treatment of binders and variables.
A well-known technique when using dependently typed programming languages such as Agda
\Fixme{Remove citations, only cite in Background section?}
\cite{Norell2008Agda}
is to define an intrinsically typed syntax tree,
where expressions are scope- and type-safe by construction and admit a total evaluation function
\cite{Augustsson1999WellTypedInterpreter}.
This construction has featured in several papers, exploring
basic operations like renaming and substitution
\cite{Allais2018UniverseOfSyntaxes}
as well as compilation to different target languages
\cite[supplemental material]{Pickard2021CalculatingDependentlyTypedCompilers}.

Performing optimisations on intrinsically typed programs, on the other hand,
has not received as much attention.
However, optimisations play an important role in compilers
and establishing their correctness is often not trivial,
with ample opportunity for mistakes.
%
In this setting, program \emph{analysis} not only identifies optimisation opportunities,
but may also need to provide a proof witness that the optimisation is safe
e.g. that some dead code is indeed not used.
For the \emph{transformation} of the intrinsically typed program,
the programmer can then rely on the compiler to check
that type- and scope-safety invariants are preserved.
However, making this clear to the compiler can be cumbersome,
especially when manipulating binders and variables.

% Compilers consist of a set of transformations,
% for example to encode language features using a simpler set of constructs.
% Usually they also perform optimisations
% to speed up the execution of the compiled program.

\vspace{1em}
\Draft{What are your research questions/contributions?}

% using "I" here. Not consistent, but "we" seems weird.
In my thesis, I want to explore this area and aim to:
\Fixme{Placeholder, elaborate!}
\begin{enumerate}
  \item collect and document program analyses and transformations that can be performed on simple expression languages with variable binders
  \item develop an understanding of potentially relevant techniques in the literature, such as datatype-generic programming on syntax trees
  \item implement several transformations on intrinsically typed expressions in the dependently-typed programming language Agda
  \item attempt machine-checked proofs of the correctness (preservation of semantics) of the implemented transformations
  \item explore the common patterns between the implemented transformations and try capturing them as reusable building blocks (e.g. as datatype-generic constructions)
\end{enumerate}
\Fixme{Think about I vs. we and make usage consistent everywhere}

\section{Background}
\Draft{What is the existing technology and literature that I'll be studying/using in my research?}

As a running example, we will consider a simple expression language with let-bindings,
variables, primitive values (integers and Booleans), and a few binary operators.
Since the optimisations in this thesis relate to variables and binders only,
the choice of possible values and additional primitive operations on them is mostly arbitrary.
Extending the language with further values and operators is trivial.
\begin{align*}
  P, Q ::=&\ v
  \\ \big||&\ P + Q
  \\ \big||&\ \Let{x} P \In Q
  \\ \big||&\ x
\end{align*}

Expressions can be bound to a variable $x$ using a $\textbf{let}$-binding.
Note that this makes the language equivalent to a restricted version of the simply typed $\lambda$-calculus,
where $\lambda$-abstraction and application can only occur together as $(\lambda x. Q)\ P$.
Encapsulating this pattern as $\Let{x} P \In Q$
simplifies parts of the analysis and
avoids the need for allowing functions as values.


\subsection{Program Analysis and Transformation}
\label{sec:background-transformations}

For now we mainly consider transformations aimed at optimising functional programs.
A large number of program analyses and and optimisations are presented in the literature
\cite{Nielson1999PrinciplesProgramAnalysis}
\cite{Santos1995CompilationByTransformation}
\cite{Jones1998TransformationOptimiser}
and used in production compilers such as the Glorious Haskell Compiler (GHC).
We generally focus on those transformations that deal with variable binders,
such as
\emph{inlining},
\emph{let-floating},
\emph{common subexpression elimination} and
\emph{dead binding elimination},
which is explained below.

\paragraph{Dead binding elimination}
An expression is not forced to make use of the whole context to which it has access.
Specifically, a let-binding introduces a new variable, but it might never be used
in the body.
Consider for example the following expression.

\begin{align*}
  &\Let{x} 42 \In \\
  &\ \ \Let{y} x + 6 \In \\
  &\ \ \ \ \Let{z} y + 7 \In \\
  &\ \ \ \ \ \ x
\end{align*}

Here, the binding for $z$ is clearly unused, as the variable never occurs in the program.
Such dead bindings can be identified by \emph{live variable analysis}
and consequently be removed.

Note that $y$ is not needed either: Removing $z$ will make $y$ unused.
Therefore, multiple iterations of live variable analysis and binding elimination can be required.
Alternatively, \emph{strongly live variable analysis} can achieve the same result in a single pass
by only considering variables to be live
if they are used in declarations of variables that are live themselves.


\subsection{Binding Representation}

\paragraph{Explicit names}
\Fixme{Should I explain free vs. bound variables, capture, \ldots?}
The syntax specified above treats variables as letters, or more generally strings,
and one can use the same representation inside a compiler.
While this is how humans usually write programs, it comes with several downsides.
For example, if we want the equality of terms to be independent
of the specific variable names chosen (\emph{$\alpha$-equivalence}),
it comes with additional complexity.
Also, there are pitfalls like variable shadowing and variable capture during substitution,
requiring the careful application of variable renamings
\cite{Barendregt1985LambdaCalculus}.

There have been multiple approaches to help compiler writers maintain the relevant invariants,
such as GHC's rapier \cite{Jones2002GHCInliner},
but these are generally still error-prone
\cite{Maclaurin2022Foil}.

\paragraph{de Bruijn indices}
With \emph{de Bruijn indices}
\cite{DeBruijn1972NamelessIndices},
each variable is instead represented as a natural number,
counting the number of nested bindings between variable occurence and its binding:
$\DeBruijn{0}$ refers to the innermost binding, $\DeBruijn{1}$ to the next-innermost etc.
If adapt we the syntax for let-bindings to omit the unnecessary name,
the example program from dead binding elimination is represented as follows:

\begin{align*}
  &\LetB 42 \In \\
  &\ \ \LetB \DeBruijn{0} + 6 \In \\
  &\ \ \ \ \LetB \DeBruijn{0} + 7 \In \\
  &\ \ \ \ \ \ \DeBruijn{2}
\end{align*}

This makes $\alpha$-equivalence of terms trivial and avoids variable capture,
but there are still opportunities for mistakes when transforming expressions.
Adding or removing a binding
requires us to add or subtract 1 from all free variables in the binding's body.
We can see this in our example when removing the innermost (unused) let-binding:

\begin{align*}
  &\LetB 42 \In \\
  &\ \ \LetB \DeBruijn{0} + 6 \In \\
  &\ \ \ \ \DeBruijn{1}
\end{align*}

\paragraph{Other representations}
There are many other techniques
\footnote{
There is an introductory blogpost by Jesper Cockx comparing options in Agda
\cite{Cockx2021RepresentationsBinding}.
}
such as higher-order abstract syntax
\cite{Pfenning1988HOAS}
and also combinations of multiple techniques, e.g. the locally nameless representation
\cite{Chargueraud2011LocallyNameless}.


\subsection{Intrinsically Typed Syntax}

%Just as the language as seen so far allows to build
Whether we use explicit names or de Bruijn indices,
the language as seen so far makes it possible to represent programs that are
\Fixme{unify language: expression/term/program}
ill-typed (e.g. adding Booleans)
or accidentally open (containing free variables).
Evaluating such a term leads to a runtime error;
the evaluation function is partial.

When implementing a compiler in a dependently typed programming language,
we can use de Bruijn indices to define \emph{intrinsically typed syntax trees},
where type- and scope-safety invariants are specified on the type level
and verified by the type checker.
This makes the evaluation function total.
Similarly, transformations on the syntax tree need to preserve the invariants.
While the meaning of the program could still change,
guaranteeing type- and scope-safety rules out
a large class of mistakes.
We will demonstrate the approach in Agda and start by defining the types that terms can have.

\begin{code}
  data U : Set where
    BOOL  : U
    NAT   : U

  interpret_ : U -> Set
  (interpret(BOOL))  = Bool
  (interpret(NAT))   = Nat
\end{code}

To know if a variable occurence is valid, one must consider its \emph{context},
the bindings that are in scope.
With de Bruijn indices in an untyped setting, it would suffice to know the number of bindings in scope.
In a typed setting, it is also necessary to know the type of each binding,
so we represent the context by a list of types: One for each binding in scope, from innermost to outermost.

\begin{code}
  Ctx = List U

  variable
    Gamma : Ctx
    sigma tau : U
\end{code}

During evaluation, each variable in scope has a value.
Together, these are called an \emph{environment} in a given context.

\begin{code}
  data Env : Ctx -> Set where
    Nil   : Env []
    Cons  : (interpret(sigma)) -> Env Gamma -> Env (sigma :: Gamma)
\end{code}

A variable then is an index into its context,
also guaranteeing that its type matches that of the binding.
Since variable |Ref sigma Gamma| acts as a proof that
the environment |Env Gamma| contains an element of type |sigma|,
variable lookup is total.

\begin{code}
  data Ref (sigma : U) : Ctx -> Set where
    Top  : Ref sigma (sigma :: Gamma)
    Pop  : Ref sigma Gamma -> Ref sigma (tau :: Gamma)
\end{code}

\begin{code}
  lookup : Ref sigma Gamma -> Env Gamma -> (interpret(sigma))
  lookup Top      (Cons v env)   = v
  lookup (Pop i)  (Cons v env)   = lookup i env
\end{code}

Now follows the definition of intrinsically typed expressions,
where an |Expr| is indexed by both
its type (|sigma : U|)
and context (|Gamma : Ctx|).
We can see how the context changes when introducing a new binding
that is then available in the body of a |Let|.

\begin{code}
  data Expr (Gamma : Ctx) : (tau : U) -> Set where
    Val   : (interpret(sigma)) -> Expr Gamma sigma
    Plus  : Expr Gamma NAT -> Expr Gamma NAT -> Expr Gamma NAT
    Let   : Expr Gamma sigma -> Expr (tau :: Gamma) tau -> Expr Gamma tau
    Var   : Ref sigma Gamma -> Expr Gamma sigma
\end{code}

This allows the definition of a total evaluator
using an environment that matches the expression's context.

\begin{code}
  eval : Expr Gamma sigma -> Env Gamma -> (interpret(sigma))
  eval (Val v)       env  = v
  eval (Plus e1 e2)  env  = eval e1 env + eval e2 env
  eval (Let e1 e2)   env  = eval e2 (Cons (eval e1 env) env)
  eval (Var x)       env  = lookup x env
\end{code}
\Fixme{Unify typesetting of v/x vs. $e_1$/$e_2$}


\subsection{Datatype-generic Programming}
% Immediately go into the syntax-related work, just a short overview, link to literature
% (might not end up being in the thesis)
\cite{Allais2018UniverseOfSyntaxes}
\Fixme{just state that there is this idea, keep it simple}


\section{Preliminary Results}
\Draft{What examples can you handle already?}
\Draft{What prototype have I built?}
\Draft{How can I generalise these results? What problems have I identified or do I expect?}

As a first step, we implemented one optimisation in Agda,
including a mechanised proof of its preservation of semantics.
The main ideas are outlined below;
the full source code is available online
\footnote{\url{https://git.science.uu.nl/m.h.heinzel/correct-optimisations}}.


\subsection{Dead Binding Elimination}
\label{sec:results-dbe}

\paragraph{Sub-contexts}
To reason about the part of a context that is live (actually used),
we introduce \emph{sub-contexts}.
Conceptually, these are contexts that admit an
\emph{order-preserving embedding} (OPE) \cite{Chapman2009TypeCheckingNormalisation}
into the original context, and we capture this notion in a single data type.
For each element of a context, a sub-context specifies whether to |Keep| or |Drop| it.

\begin{code}
data SubCtx : Ctx -> Set where
  Empty  : SubCtx []
  Drop   : SubCtx Gamma → SubCtx (tau :: Gamma)
  Keep   : SubCtx Gamma → SubCtx (tau :: Gamma)
\end{code}

The context uniquely described by a sub-context is
then given by a function |floor_ : SubCtx Gamma -> Ctx|,
and we further know its embedding.

We now define |c= : SubCtx Gamma -> SubCtx Gamma -> Set|,
stating that one sub-context is a subset of the other.
Its witnesses are unique, which simplifies the correctness proofs.
A similar relation on |Ctx| does not have this property
(e.g. |[NAT]| can be embedded into |[NAT, NAT]| either by keeping the first element or the second),
which would complicate equality proofs on terms including witnesses of |c=|.

From now on, we will only consider expressions
|Expr (floor(Delta)) tau| in some sub-context.
Initially, we take |Delta = all Gamma : SubCtx Gamma|,
the complete sub-context of the original context.

\paragraph{Analysis}
Now we can annotate each expression with its \emph{live variables},
the sub-context |Delta' c= Delta| that is really used.
To that end, we define annotated expressions |LiveExpr Delta Delta' tau|.
While |Delta| is treated as |Gamma| was before, |Delta'| now only contains live variables,
starting with a singleton sub-context at the variable usage sites.

\begin{code}
data LiveExpr : (Delta Delta' : SubCtx Gamma) (tau : U) -> Set where
  Let : LiveExpr Delta Delta1 sigma ->
        LiveExpr (Keep Delta) Delta2 tau ->
        LiveExpr Delta (Delta2 \/ pop Delta2) tau
\end{code}

To create such annotated expressions, we need to perform
some static analysis of our source programs.
The function |analyse| computes an existentially qualified live sub-context |Delta'|
together with a matching annotated expression.
The only requirement we have for it is that we can forget the annotations again,
with |forget . analyse == id|.

\begin{code}
  analyse : Expr (floor(Delta)) tau -> (Exists (Delta') (SubCtx Gamma)) LiveExpr Delta Delta tau
  forget  : LiveExpr Delta Delta' tau -> Expr (floor(Delta)) tau
\end{code}

% NOTE:
% Maybe add a note that LiveExpr is overspecified.
% Instead of |Delta1 \/ Delta2| we could have any |Delta'| containing |Delta1| and |Delta2|.

\paragraph{Transformation}
Note that we can evaluate |LiveExpr| directly, differing from |eval| mainly
in the |Let|-case, where we match on |Delta2| to distinguish whether the bound variable is live.
If it is not, we directly evaluate the body, ignoring the bound declaration.
Another important detail is that evaluation works under any environment containing (at least) the live context.

\begin{code}
  evalLive : LiveExpr Delta Delta' tau -> Env (floor(DeltaU)) -> (Irrelevant(Delta c= DeltaU)) -> (interpret(tau))
\end{code}

This \emph{optimised semantics} shows that we can do a similar program transformation
and will be useful in its correctness proof.
The implementation simply maps each constructor to its counterpart in |Expr|,
with some renaming
(e.g. from |(floor(Delta1))| to |(floor(Delta1 \/ Delta2)|)
and the abovementioned case distinction.

\begin{code}
  dbe : LiveExpr Delta Delta' tau -> Expr (floor(Delta')) tau
  dbe (Let {Delta1} {Drop Delta2} e1 e2) = injExpr2 Delta1 Delta2 (dbe e2)
  dbe (dots)
\end{code}

As opposed to |forget|, which stays in the original context,
here we remove unused variables, only keeping |(floor(Delta'))|.

\paragraph{Correctness}
We want to show that dead binding elimination preserves semantics:
|eval . dbe . analyse == eval|.
Since we know that |forget . analyse == id|,
it is sufficient to show the following:

\begin{code}
  eval . dbe == eval . forget
\end{code}

The proof gets simpler if we split it up using the optimised semantics.

\begin{code}
  eval . dbe == evalLive = eval . forget
\end{code}

The actual proof statements are more involved,
since they quantify over the expression and environment used.
As foreshadowed in the definition of |evalLive|, the statements are also generalised
to evaluation under any |Env (floor(DeltaU))|,
as long as it contains the live sub-context.
This gives us more flexibility when using the inductive hypothesis.

Both proofs work inductively on the expression, with most cases being a straight-forward congruence.
The interesting one is again |Let|, where we split cases on the variable being used or not
and need some auxiliary facts about evaluation, renaming and sub-contexts.

\paragraph{Iterating the Optimisation}
As discussed in section \ref{sec:background-transformations},
more than one pass of dead binding elimination can be required to remove all unused bindings.
While in our simple setting all these bindings could be identified in a single pass
using strong live variable analysis,
in general it can be useful to simply iterate the optimisation until a fixpoint is reached.

Consequently, we keep applying |dbe . analyse| as long as the number of bindings decreases.
Such an iteration is not structurally recursive, so Agda's termination checker needs our help.
We observe that the algorithm must terminate
since the number of bindings decreases with each iteration (but the last) and cannot become negative.
This corresponds to the ascending chain condition in program analysis literature
\cite{Nielson1999PrinciplesProgramAnalysis}.
To convince the termination checker, we use well-founded recursion
\cite{Bove2014PartialityRecursion}
on the number of bindings.

The correctness of the iterated implementation
follows directly from the correctness of each individual iteration step.


\subsection{$\lambda$-calculus}
\label{sec:results-lambda}

Most functional languages are based on some variant of the $\lambda$-calculus.
Extending our expression language with $\lambda$-abstractions and function application
would therefore make our work more applicable to these settings
and provide an additional source of bindings with new kinds of transformations.

We implemented a prototype of this extended language,
and adapted dead binding elimination to accommodate the new constructors.
The additional cases are very similar to the existing ones,
but the possible results of evaluation now include functions.
Therefore, reasoning about semantic equivalance using propositional equality
requires postulating function extensionality.
This does not impact the soundness of the proof
and could be avoided by moving to a different setting,
such as homotopy type theory.
\Fixme{Citation just for mentioning HoTT?}

While these changes were unproblematic,
$\lambda$-abstractions could make other optimisations more challenging,
so they remain a prototype for now and are not included in our core language.
% However, we hope to add full support for them later on.
% This would also give us access to further optimisations
% such as removal of unused function arguments
% and some of the local rewrites mentioned above.


\section{Timetable and Planning}

\subsection{Further Work}
\label{sec:further-work}
\Draft{What will I do with the remainder of my thesis?}

There is a large number of possible directions to explore.
While working on all of them is not feasible,
this section gives an overview of the most promising ones.


\subsubsection{Strongly Live Variable Analysis}

Instead of iterating the dead binding elimination as defined above,
the same result can be achieved in a single pass
using strongly live variable analysis, as explained in section \ref{sec:background-transformations}.

An initial prototype still contains unresolved complications in the correctness proof.
These do not seem to be fundamental limitations and could be worth investigating further.


\subsubsection{Other Transformations}

\paragraph{Inlining}
We will focus on the simplest form of inlining,
which only replaces a variable occurrence
with the corresponding declaration.
Sometimes, inlining is also understood to involve removing the inlined binding
or even performing beta reduction wherever inlining produces a beta redex
\cite{Jones2002GHCInliner},
but this can be taken care of by other transformations.

On the language we defined, inlining is always possible and semantics-preserving.
The analysis only needs to specify which variables should be inlined,
usually based on some heuristics involving the size of declaration,
number of variable occurrences and similar factors.

\paragraph{Let-floating}
It is usually advantageous for bindings to be \emph{floated inward} as far as possible,
potentially avoiding their evaluation and uncovering opportunities for other optimisations.
In other cases, it can be useful to \emph{float outward} of specific constructs
to avoid performing the same work multiple times
\cite{Jones1996LetFloating}.

To make sure that moving a binding is valid,
the analysis currently only needs to ensure that scope correctness is preserved,
i.e. variable occurrences are never moved above their declaration or vice versa.
When limiting the transformation to either moving the binding as far as possible
or just across a single constructor,
bindings only need to be annotated with a single bit of information -- to move or not to move.
However, it might be interesting to allow more fine-grained control over the desired location,
which would require a more sophisticated type for the analysis result.

\paragraph{Common subexpression elimination}
The aim of this transformation is to find subexpressions that occur multiple times
and replace them with a variable that is bound to this expression
and only needs to be evaluated once.
% A basic implementation keeps track of the declaration of all bindings in scope
% to find any occurrences of the same expression.
For a basic implementation it suffices to try finding occurrences of expressions
that are the same as the declaration of a binding already in scope.
These can then be replaced by the bound variable,
reducing both code size and work performed during evaluation.

Capturing the results of such a program analysis will require some changes
compared to the variable liveness annotations in dead binding elimination,
since being replaceable by a variable is not just a property of a term,
but also its context.

This basic version potentially misses many opportunities,
since it relies on the right terms to be available as a variable in scope.
Consider for example expressions like
$x * 2 + x * 2$,
where the duplicated work can only be avoided by introducing a new let-binding.
Some additional opportunities can be exposed by a preprocessing step,
breaking down expressions into sequences of small let-bindings and floating them upwards,
but making this work well is tricky.
One also needs to consider that these additional let-bindings affect other transformations,
unless they are removed again after common subexpression elimination.

\paragraph{More powerful common subexpression elimination}
Another approach is to put more work into identifying common subexpressions
and making the transformation itself introduce a shared binding
at a suitable point.
Making this analysis efficient is challenging,
but this is not a major concern for us.
Our focus is on defining the right structure for the analysis results
and applying the transformation accordingly.

\paragraph{Local rewrites}
There is a number of local transformations
that simply rewrite a specific pattern into an equivalent one.
Most examples are always valid to be performed:
\begin{itemize}
  \item constant folding and identities, \\
    e.g. $E + 0 \Rightarrow E$
  \item turning beta redexes into let-bindings, \\
    i.e. $(\lambda x. Q) P \Rightarrow \Let{x} P \In Q$
  \item floating let-bindings out of function application, \\
    i.e. $(\Let{x} P \In Q)\ R \Rightarrow \Let{x} P \In Q\ R$
\end{itemize}
Showing that such a rewrite preserves semantics should be straight-forward,
but usually we want to do a single pass over the program
that applies the rewrite wherever possible.
The correctness of this operation can be shown by structural induction,
but this is pure boilerplate code, identical for each rewrite rule.

We aim to factor out the redundant parts and handle local rewrites in a uniform way.


\subsubsection{Extending the Language}

Adding constructs to the language gives us access to new transformations,
for example to optimise their evaluation or encode them using existing constructs.
However, each of them complicates the language and comes with its own challenges.
The amount of code required is generally proportional to the product of
number of language constructs and number of transformations.

One example are $\lambda$-abstractions (section \ref{sec:results-lambda}),
which we hope to fully support later on.
This would also allow us to do transformations
such as removal of unused function arguments
and some of the local rewrites mentioned above.
We outline further potential extensions and the consequences of adding them to the language.

\paragraph{Recursive Bindings}
In a recursive let-binding, the bound variable is available in its own declaration.
While this only requires a small change in the definition of the syntax tree,
evaluation can now diverge.
The treatment of semantics requires significant changes to account for this partiality
\cite{Capretta2005GeneralRecursion}
\cite{McBride2015TuringCompletenessTotallyFree}
\cite{Danielsson2012PartialityMonad}.
Some transformations then require a form of guaranteeing purity of strict bindings,
since (re)moving bindings with side effects can change the program's semantics.

\paragraph{Mutually recursive binding groups}
Since mutual recursion allows multiple bindings to refer to each other,
the current approach of handling one binding at a time is not sufficient.
Instead, we need to allow a list of simultaneous declarations
where the scope of each is extended with a list of variables.
Working with this structure is expected to be laborious.
Similarly, it is currently unclear whether Allais' universe of syntax
can express this construction.

On the other hand, intrinsically typed implementations
of related transformations could be instructive
precisely because of the complexity of the bindings involved.
An example is
splitting binding groups into strongly connected components.

\paragraph{Nonstrict bindings}
Languages can contain strictly evaluated, nonstrictly evaluated or both types of bindings.
Once there are side effects (such as non-termination),
the strictness of bindings plays an important role
for semantics preservation of transformations.
While inlining or floating a nonstrict let-bindings is always valid,
the same is only true for strict let-bindings if they are pure,
i.e. free of side effects
\cite{Jones2002GHCInliner}.

\paragraph{Branching}
The presence of a branching construct like \emph{if-then-else} expressions
makes some analyses more interesting since control flow is not known upfront.
In addition, some optimisations become more worthwile:
\begin{itemize}
  \item pushing a binding into a single branch where it is used avoids unnecessary computation,
  \item bindings present in all branches can be hoisted out to reduce code size,
  \item having information about the possible values of expressions can allow to remove unreachable branches.
\end{itemize}

These aspects however are not the main focus of this work;
most of the actual transformations are unaffected.

\paragraph{Datatypes with pattern matching}
Adding algebraic datatypes is a much larger change,
but also provides us with a new source of bindings and related transformations.
GHC for example offers a wealth of inspiration with the \emph{case-of-case}-optimisation and others
\cite{Jones1998TransformationOptimiser}.


\subsubsection{Restricted Language Forms}

Practical compilers often enforce additional restrictions
on the structure of their intermediate languages
to simplify transformations and compilation to a machine language.
Popular choices include \emph{continuation passing style} (CPS)
and \emph{A-normal form} (ANF)
\cite{Flanagan1993EssenceCompilingContinuations}.
The Glorious Haskell Compiler (GHC) for example
performs a transformation called \emph{CorePrep}
to ensure (among others) the invariant
that all function arguments are atoms,
i.e. literals or variables.
This simplifies further transformations on the language
\cite{Santos1995CompilationByTransformation}.

It could be investigated how the introduction of similar restrictions
impacts the transformations we study, including their proof of correctness.
Furthermore, the transformation into the restricted form itself can be studied.


\subsubsection{Generalisation}
Ideally, further exploration will lead to the discovery of common patterns
and useful strategies for performing optimisations on intrinsically typed syntax trees.
One particular question is whether it is useful to always separate program analysis
and transformation using an annotated version of the syntax tree,
as currently done with dead binding elimination.


\subsubsection{Syntax-generic programming}
To avoid boilerplate code and make our work more reusable,
we are investigating the possibility to work with syntax-generic definitions of operations and proofs.
Capturing common patterns and operations in the form of general helper functions
could be insightful and reduce the effort of adding further transformations.


\subsection{Schedule}
\Draft{Give an approximate estimation/timetable for what you will do and when you will be done.}

The thesis deadline is on 09.06.2023.
To allow for sufficient grading time,
I will submit my thesis until 26.05.2023, the end of week 21.
Leaving two weeks for holidays and one as buffer time, I will have about 18 weeks of time available.
\Fixme{Talk about dependencies more explicitly?}
The work can be split into four main phases, each with an estimated time frame.

\subsubsection{Initial Experimentation (4 weeks)}

To give me the practical experience necessary to discover and encode general ideas,
I will attempt the following practical tasks:
\begin{itemize}
  \item finish the implementation of dead binding elimination with strong live variable analysis
  \item implement inlining
  \item implement let-floating
  \item implement rewrite rules
  \item port dead binding elimination to the \texttt{generic-syntax} library by Allais et al.
\end{itemize}
At the same time, this phase will involve further reading to
deepen my understanding of datatype- and syntax-generic programming, and
explore potentially relevant ideas, such as ornamentation and coeffects.
\Fixme{cite?}

\subsubsection{Generalise and Extend (6 weeks)}

\begin{itemize}
  \item sketch out general ideas, both conceptually and in code
  \item challenge the approach by adding additional language features (primarily recursive bindings)
  \item implement more sophisticated transformations, e.g. common subexpression elimination
\end{itemize}

\subsubsection{Optional Goals (2 weeks)}

As time permits, I will continue by working on some of the remaining items
layed out in section \ref{sec:further-work}
that seem feasible and interesting based on the experience gained.
There might also be completely new ideas spawned by the previous work.

\subsubsection{Writing (6 weeks)}

Throughout the whole time,
I aim to continiously draft descriptions
of the ideas developed and features implemented.
These documents will then be refined towards the end
and serve as the basis for writing the thesis.
The last week should be reserved for proofreading.



\bibliographystyle{acm}
\bibliography{../correct-optimisations}{}

\pagebreak
\appendix
\section{Ethics Quick Scan}
\Draft{(anonymised report)}
\Fixme{Insert!}

\end{document}
