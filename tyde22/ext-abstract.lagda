\documentclass[sigplan,nonacm,screen]{acmart}

% workaround, see https://github.com/kosmikus/lhs2tex/issues/82
\let\Bbbk\undefined

%include agda.fmt
%include custom.fmt

% https://icfp22.sigplan.org/home/tyde-2022#Call-for-Papers

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{stmaryrd}
\usepackage{listings}
\usepackage{xcolor}
\usepackage{xspace}
\usepackage{natbib}

\citestyle{acmauthoryear}

\title{Provingly Correct Optimisations on Intrinsically Typed Expressions}
\subtitle{Extended Abstract}

\author{Matthias Heinzel}
\affiliation{%
  \institution{Utrecht University}
  \city{Utrecht}
  \country{Netherlands}}
\email{m.h.heinzel@@students.uu.nl}

\acmConference[TyDe’22]{Workshop on Type-Driven Development}{September 11}{Ljubljana, Slovenia}

\date{\today}

\begin{document}

\maketitle

\section{Introduction}

When writing a compiler for a functional programming language,
an important consideration is the treatment of binders and variables.
A well-known technique when using dependently typed programming languages such as Agda
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
In this setting, program \emph{analysis} not only needs to identify optimisation opportunities,
but provide a proof witness that the optimisation is safe,
e.g. that some dead code is indeed not used.
For the \emph{transformation} of the intrinsically typed program,
the programmer can then rely on the compiler to check the relevant invariants,
but it can be cumbersome to make it sufficiently clear that type- and scope-safety are preserved,
especially when manipulating binders and variables.

% May want to cite Graham's (draft) paper - it's as easy
% as 1,2,3 that argues that studying semantics is best done in a
% setting that is as simple as possible.

% Not sure how to plug the Nielson book here, maybe just leave it out?
% list interesting optimisations?

Since our work is still in progress,
we will mainly present a specific optimisation, \emph{dead binding elimination}.
It is implemented by first annotating expressions with variable usage information
and then removing bindings that turn out to be unused.
We further prove that the optimisation is semantics-preserving.


\section{Dead Binding Elimination}

\subsection{Intrinsically Typed Expressions with Binders}

We define a simple, typed expression language with let-bindings,
variables, primitive values (integers and Booleans), and a few binary operators.
Since the optimisations we are interested in relate to variables and binders only,
the choice of possible values and additional primitive operations on them is mostly arbitrary.

\begin{align*}
  P, Q ::= v
  \ \big||\  P + Q
  \ \big||\  \ldots
  \ \big||\  \textbf{let } x = P \textbf{ in } Q
  \ \big||\  x
\end{align*}

In Agda, the type of expressions |Expr| is indexed by its return type (|tau : U|)
and context (|Gamma : Ctx|).

Each free variable is a de Bruijn index into the context and acts as a proof that
the context contains an element of the matching type.
We can see how the context changes when introducing a new binding:

\begin{code}
data Expr (Gamma : Ctx) : (tau : U) -> Set where
  Let   : Expr Gamma sigma -> Expr (tau :: Gamma) tau -> Expr Gamma tau
  (dots)
\end{code}

This allows the definition of a total evaluator
using a matching environment:

\begin{code}
  eval : Expr Gamma tau -> Env Gamma -> (interpret(tau))
\end{code}


\subsection{Sub-contexts}

% NOTE: cite \emph{A correct-by-construction conversion to combinators}? It's quite similar.
% TODO: Call it SubCtx?

Note that an expression is not forced to make use of the whole context
to which it has access.
Specifically, a let-binding introduces a new element into the context,
but it might never be used.

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
then given by a function |(floor (_)) : SubCtx Gamma -> Ctx|,
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

\subsection{Live Variable Analysis}

Now we can annotate each expression with its \emph{live variables},
the sub-context |Delta' c= Delta| that is really used.
To that end, we define annotated expressions |LiveExpr Delta Delta' tau|.
While |Delta| is treated as |Gamma| was before, |Delta'| now only contains live variables,
starting with a singleton sub-context at the variable usage sites.

% TODO: too wide?
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

\subsection{Transformation}

Note that we can evaluate |LiveExpr| directly, differing from |eval| mainly
in the |Let|-case, where we match on |Delta2| to distinguish whether the bound variable is live.
If it is not, we directly evaluate the body, ignoring the bound declaration.
Another important detail is that evaluation works under any environment containing (at least) the live context.

\begin{code}
  evalLive :
    LiveExpr Delta Delta' tau -> Env (floor(DeltaU)) -> (Irrelevant(Delta c= DeltaU)) -> (interpret(tau))
\end{code}

This \emph{optimised semantics} shows that we can do a similar program transformation
and will be useful in its correctness proof.
The implementation simply maps each constructor to its counterpart in |Expr|,
with some renaming
(e.g. from |(floor(Delta1))| to |(floor(Delta1 \/ Delta2)|)
and the abovementioned case distinction.

% TODO: slightly too wide?
\begin{code}
  dbe : LiveExpr Delta Delta' tau -> Expr (floor(Delta')) tau
  dbe (Let {Delta1} {Drop Delta2} e1 e2) = injExpr2 Delta1 Delta2 (dbe e2)
  dbe (dots)
\end{code}

As opposed to |forget|, which stays in the original context,
here we remove unused variables, only keeping |(floor(Delta'))|.

\subsection{Correctness}

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

\subsection{Iterating the Optimisation}

A binding that is removed can contain the only occurrences of some other variable.
This makes another binding dead, allowing further optimisation when running the algorithm again.
While in our simple setting all these bindings could be identified in a single pass
using \emph{strong live variable analysis},
in general it can be useful to simply iterate the optimisation until a fixpoint is reached.

Such an iteration is not structurally recursive, so Agda's termination checker needs our help.
We observe that the algorithm must terminate
since the number of bindings decreases with each iteration (but the last) and cannot become negative.
This is the same as the ascending chain condition in program analysis literature
\cite{Nielson1999PrinciplesProgramAnalysis}.
To convince the termination checker, we use \emph{well-founded recursion} \cite{Bove2014PartialityRecursion}
on the number of bindings.

The correctness follows directly from the correctness of each individual iteration step.

\section{Preliminary Results}

The implementation and correctness proof of dead binding elimination are complete,
the Agda source code is available online
\footnote{\url{https://github.com/mheinzel/correct-optimisations}}.
One interesting observation is that the correctness proof does not rely on how
|analyse| computes the annotations.
At first, this does not seem particularly useful,
but for other optimisations the analysis might use complex, frequently changing heuristics to decide
which transformations are worth it.

We are currently extending the expression language
with $\lambda$-abstractions.
While some increase in complexity is necessary to eliminate applications of functions that do not use their argument,
the correctness proof seems to stay relatively simple.

We are further investigating additional binding-related transformations,
such as moving bindings up or down in the syntax tree.
Another interesting type of optimisation is avoidance of redundant computations
using \emph{available expression analysis}.
An example is \emph{common subexpression elimination},
where subexpressions get replaced by variables bound to equivalent declarations
(pre-existing or newly created).

Between the different optimisations,
we hope to discover common patterns and refine our approach,
providing useful strategies for performing optimisations in intrinsically typed compilers.
% or more generally, manipulating well-typed well-scoped syntax trees?

\bibliographystyle{ACM-Reference-Format}
\bibliography{../correct-optimisations}{}

\end{document}
