\documentclass[draft]{report}

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
\usepackage[pdfencoding=auto, psdextra]{hyperref}  % for \lambda in section title
\usepackage{colortbl}
\usepackage{todonotes}
\usepackage[nottoc,notlot,notlof]{tocbibind}
\usepackage{pdfpages}

\newcommand{\Outline}[1]{}
% \newcommand{\Outline}[1]{\todo[inline,backgroundcolor=gray!30]{#1}}

\newcommand{\Fixme}[1]{}
% \newcommand{\Fixme}[1]{\todo[color=orange!30]{#1}}

\newcommand{\Let}[1]{\textbf{let } #1 = }
\newcommand{\LetB}{\textbf{let }} % using de Bruijn indices
\newcommand{\In}{\textbf{ in }}
\newcommand{\DeBruijn}[1]{\langle #1 \rangle}

\newcommand{\X}{\cellcolor{gray}}
\newcolumntype{L}{>{\centering\arraybackslash}X}
\newcommand{\Week}[1]{\tiny #1}

\setcounter{tocdepth}{1}

\title{Analysis and Transformation of Intrinsically Typed Syntax}
\author{Matthias Heinzel\\Utrecht University}
\date{\today}

\begin{document}

\maketitle
% TODO: M.Sc. Thesis, advisors, logo?

\tableofcontents


\chapter{Introduction}

\Fixme{Copied from proposal, adapt}
When writing a compiler for a programming language,
an important consideration is the treatment of binders and variables.
A well-known technique when using dependently typed programming languages such as Agda
\cite{Norell2008Agda}
is to define an intrinsically typed syntax tree,
where expressions are scope- and type-correct by construction and admit a total evaluation function
\cite{Augustsson1999WellTypedInterpreter}.
This construction has featured in several papers, exploring
basic operations like renaming and substitution
\cite{Allais2018UniverseOfSyntaxes}
as well as compilation to different target languages
\cite[online supplementary material]{Pickard2021CalculatingDependentlyTypedCompilers}.

At the same time, there are large classes of important transformations
that have not yet received much attention in an intrinsically typed setting.
Optimisations, for example, play a central role in practical compilers
and establishing their correctness is often not trivial,
with ample opportunity for binding-related mistakes
\cite{SpectorZabusky2019EmbracingFormalizationGap}
\cite{Maclaurin2022Foil}.
Letting the type checker keep track of important invariants
promises to remove common sources of bugs.
A mechanised proof of semantics preservation can increase confidence further.

In return for the correctness guarantees, some additional work is required.
Program \emph{analysis} not only needs to identify optimisation opportunities,
but potentially also provide a proof witness that the optimisation is safe,
e.g. that some dead code is indeed unused.
For the \emph{transformation} of the intrinsically typed program,
the programmer then has to convince the type checker
that type- and scope-correctness invariants are preserved,
which can be cumbersome.
The goal of this thesis is to understand these consequences better and make the following contributions:
\Outline{What are your research questions/contributions?}

\begin{enumerate}
  \item collect and document program analyses and transformations that can be performed on simple expression languages with variable binders
  \item implement several of these transformations using intrinsically typed expressions in the dependently-typed programming language Agda
  \item provide machine-checked proofs of the correctness (preservation of semantics) of the implemented transformations
  \item attempt to apply relevant techniques from the literature, such as datatype-generic programming on syntax trees
  \item identify common patterns and try capturing them as reusable building blocks (e.g. as datatype-generic constructions)
\end{enumerate}

The Ethics and Privacy Quick Scan of the Utrecht University Research Institute of Information and Computing Sciences was conducted (see the end of the document).
It classified this research as low-risk with no fuller ethics review or privacy assessment required.


\chapter{Background}

As a running example, we will consider a simple expression language with let-bindings,
variables, primitive values (integers and Booleans), and a few binary operators.
Since the transformations in this thesis primarily relate to variables and binders,
the choice of possible values and additional primitive operations on them is mostly arbitrary.
Extending the language with further values and operators is trivial.
\begin{align*}
  P, Q ::=&\ v
  \\ \big||&\ P + Q
  \\ \big||&\ \Let{x} P \In Q
  \\ \big||&\ x
\end{align*}

An expression can be bound to a variable $x$ using a $\textbf{let}$-binding.
Note that this makes the language equivalent to a restricted version of the simply typed $\lambda$-calculus,
where $\lambda$-abstraction and application can only occur together as $(\lambda x. Q)\ P$.
Encapsulating this pattern as $\Let{x} P \In Q$
simplifies parts of the analysis and
avoids the need for allowing functions as values.


\section{Program Analysis and Transformation}
\label{sec:background-transformations}

For now we mainly consider transformations aimed at optimising functional programs.
A large number of program analyses and optimisations are presented in the literature
\cite{Nielson1999PrinciplesProgramAnalysis}
\cite{Santos1995CompilationByTransformation}
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
Consider for example the following expression:

\begin{align*}
  &\Let{x} 42 \In \\
  &\ \ \Let{y} x + 6 \In \\
  &\ \ \ \ \Let{z} y + 7 \In \\
  &\ \ \ \ \ \ x
\end{align*}

Here, the binding for $z$ is clearly unused, as the variable never occurs in the body.
Such dead bindings can be identified by \emph{live variable analysis}
and consequently be removed.

Note that $y$ is not needed either: Removing $z$ will make $y$ unused.
Therefore, multiple iterations of live variable analysis and binding elimination might be required.
Alternatively, \emph{strongly live variable analysis} can achieve the same result in a single pass
by only considering variables to be live
if they are used in declarations of variables that are live themselves.


\section{Binding Representation}

\paragraph{Explicit names}
The syntax specified above treats variables as letters, or more generally strings,
and one can use the same representation inside a compiler.
While this is how humans usually write programs, it comes with several downsides.
For example, some extra work is necessary
if we want the equality of expressions to be independent of the specific variable names chosen
(\emph{$\alpha$-equivalence}).
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
If we adapt the syntax for let-bindings to omit the unnecessary variable name,
the example expression from dead binding elimination is represented as follows:

\begin{align*}
  &\LetB 42 \In \\
  &\ \ \LetB \DeBruijn{0} + 6 \In \\
  &\ \ \ \ \LetB \DeBruijn{0} + 7 \In \\
  &\ \ \ \ \ \ \DeBruijn{2}
\end{align*}

This makes $\alpha$-equivalence of expressions trivial and avoids variable capture,
but there are still opportunities for mistakes during transformations.
Adding or removing a binding
requires us to add or subtract 1 from all free variables in the binding's body.
We can see this in our example when removing the innermost (unused) let-binding:

\begin{align*}
  &\LetB 42 \In \\
  &\ \ \LetB \DeBruijn{0} + 6 \In \\
  &\ \ \ \ \DeBruijn{1}
\end{align*}

\paragraph{Other representations}
There are many other techniques%
\footnote{
There is an introductory blogpost
\cite{Cockx2021RepresentationsBinding}
comparing options available in Agda.
}
such as higher-order abstract syntax
\cite{Pfenning1988HOAS}
and also combinations of multiple techniques, e.g. the locally nameless representation
\cite{Chargueraud2011LocallyNameless}.


\section{Intrinsically Typed Syntax}

%Just as the language as seen so far allows to build
Whether we use explicit names or de Bruijn indices,
the language as seen so far makes it possible to represent expressions
that are ill-typed (e.g. adding Booleans)
or accidentally open (containing free variables).
Evaluating such an expression leads to a runtime error;
the evaluation function is partial.

When implementing a compiler in a dependently typed programming language,
we can use de Bruijn indices to define \emph{intrinsically typed syntax trees},
where type- and scope-correctness invariants are specified on the type level
and verified by the type checker.
% MAYBE: mention inductive families (Dybjer)?
This makes the evaluation function total
\cite{Augustsson1999WellTypedInterpreter}.
Similarly, transformations on the syntax tree need to preserve the invariants.
While the semantics of the expression could still change,
guaranteeing type- and scope-correctness rules out
a large class of mistakes.
We will demonstrate the approach in Agda and start by defining the types that expressions can have.
\Fixme{rename to \emph{sorts}?}

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
% MAYBE: Say that we use Agda's variable feature to make things more concise?

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


% \section{Syntax-generic Programming}
% Immediately go into the syntax-related work, just a short overview, link to literature
% (might not end up being in the thesis)
% \cite{Allais2018UniverseOfSyntaxes}
% \Fixme{just state that there is this idea, keep it simple}


\chapter{Results}

\Fixme{Copied from proposal, adapt}
As a first step, we implemented one optimisation in Agda,
including a mechanised proof of its preservation of semantics.
The main ideas are outlined below;
the full source code is available online%
\footnote{\url{https://git.science.uu.nl/m.h.heinzel/correct-optimisations}}.


\section{Dead Binding Elimination}
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

We now define |_c=_ : SubCtx Gamma -> SubCtx Gamma -> Set|,
stating that one sub-context is a subset of the other.
Its witnesses are unique, which simplifies the correctness proofs.
A similar relation on |Ctx| does not have this property
(e.g. |[NAT]| can be embedded into |[NAT, NAT]| either by keeping the first element or the second),
which would complicate equality proofs on terms including witnesses of |_c=_|.

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
  (dots)
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
  (dots)
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
  evalLive == eval . dbe
  evalLive == eval . forget
\end{code}

The actual proof statements in Agda are more involved,
since they quantify over the expression and environment used for evaluation.
As foreshadowed in the definition of |evalLive|, the statements are also generalised
to evaluation under any |Env (floor(DeltaU))|,
as long as it contains the live sub-context.
This gives us more flexibility when using the inductive hypothesis.

Both proofs work inductively on the expression, with most cases being a straight-forward congruence.
The interesting one is again |Let|, where we split cases on the variable being used or not
and need some auxiliary facts about evaluation, renaming and sub-contexts.

\paragraph{Iterating the Optimisation}
As discussed in chapter \ref{sec:background-transformations},
more than one pass of dead binding elimination might be necessary to remove all unused bindings.
While in our simple setting all these bindings could be identified in a single pass
using strongly live variable analysis,
in general it can be useful to simply iterate optimisations until a fixpoint is reached.

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


\section{$\lambda$-calculus with Let-bindings}
\label{sec:results-lambda}

Most functional languages are based on some variant of the $\lambda$-calculus.
Extending our expression language with $\lambda$-abstractions and function application
would therefore make our work more applicable to these settings
and provide an additional source of bindings with new kinds of transformations.

We implemented a prototype of this extended language,
and adapted dead binding elimination to accommodate the new constructors.
The additional cases are very similar to the existing ones,
but the possible results of evaluation now include functions.
Therefore, reasoning about semantic equivalence using propositional equality
requires postulating function extensionality.
This does not impact the soundness of the proof
and could be avoided by moving to a different setting,
such as homotopy type theory
\cite{Univalent2013HomotopyTypeTheory}.

While these changes were unproblematic,
$\lambda$-abstractions could make other transformations more challenging,
so they remain a prototype for now and are not included in our core language.


\bibliographystyle{plainurl}
\bibliography{../correct-optimisations}{}


% TODO: Appendix heading (incl. TOC) via chapter?
% But keep embedded pdf on the same page.
\appendix
\Outline{(anonymised report)}
\includepdf[pages=1,scale=0.7,pagecommand=\label{sec:ethics-quick-scan}]{ethics-privacy-quick-scan-results-anonymised.pdf}
\includepdf[pages=2-,scale=0.7,pagecommand=\thispagestyle{plain}]{ethics-privacy-quick-scan-results-anonymised.pdf}

\end{document}
