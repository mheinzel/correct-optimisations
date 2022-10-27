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
\usepackage{tabularx}
\usepackage{todonotes}

% \newcommand{\Draft}[1]{}
% \newcommand{\Fixme}[1]{}
\newcommand{\Draft}[1]{\todo[inline,backgroundcolor=gray!30]{#1}}
\newcommand{\Fixme}[1]{\todo[color=orange!30]{#1}}
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
\cite{norell2007agda}
is to define an intrinsically typed syntax tree,
where expressions are scope- and type-safe by construction and admit a total evaluation function
\cite{augustsson1999intrinsic}.
This construction has featured in several papers, exploring
basic operations like renaming and substitution
\cite{allais2018universe}
as well as compilation to different target languages
\cite[supplemental material]{pickard2021calculating}.

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

\vspace{1em}
\Draft{What are your research questions/contributions?}

In my thesis, I want to explore this area and aim to:
\Fixme{Placeholder, elaborate!}
\begin{enumerate}
  \item collect and document program analyses and transformations that can be performed on simple expression languages with variable binders
  \item develop an understanding of potentially relevant techniques in the literature, such as datatype-generic programming on syntax trees
  \item implement several transformations on intrinsically typed expressions in the dependently-typed programming language Agda
  \item attempt machine-checked proofs of the correctness (preservation of semantics) of the implemented transformations
  \item explore the common patterns between the implemented transformations and try capturing them as re-usable building blocks (e.g. as datatype-generic constructions)
\end{enumerate}

\section{Background}
\Draft{What is the existing technology and literature that I'll be studying/using in my research?}

As a running example, I use a simple expression language with let-bindings,
variables, primitive values (integers and Booleans), and a few binary operators.
Since the optimisations in this thesis relate to variables and binders only,
the choice of possible values and additional primitive operations on them is mostly arbitrary.
Extending the language with further values and operators is trivial.
\begin{align*}
  P, Q ::=&\ v
  \\ \big||&\ P + Q
  \\ \big||&\ \textbf{let } x = P \textbf{ in } Q
  \\ \big||&\ x
\end{align*}

Expressions can be bound to a variable $x$ using the $\textbf{let}$ construction.
Note that this makes the language equivalent to a restricted version of the simply typed $\lambda$-calculus,
where $\lambda$-abstraction and application can only occur together as $(\lambda x. Q) P$.
Encapsulating this pattern as $\textbf{let } x = P \textbf{ in } Q$
simplifies parts of the analysis and
avoids the need for allowing functions as values.

\subsection{Program Analysis and Transformation}

Optimisations are important.
\Fixme{Elaborate!}

A large number of program analyses and and optimisations are presented in the literature
\cite{nielson1999analysis}.
The focus of this work is on those that deal with variable binders,
some of which are explained below.

\paragraph{Live variable analysis}
Note that an expression is not forced to make use of the whole context to which it has access.
Specifically, a let-binding introduces a new element into the context, but it might never be used
in the body.
One commonly wants to identify such unused bindings so they can be removed from the program.
This can be achieved using \emph{live variable analysis}.
\Fixme{Explain (with example?)}
\Fixme{Also explain \emph{strong} version?}

\subsection{Intrinsically Typed Syntax}

The syntax specified above treats variables as letters, or more generally strings.
To prevent complications with bindings of the same variable name shadowing each other
and to make equality of terms independent of the specific names chosen
(\emph{$\alpha$-equivalence}),
compilers often represent variables in a different way.
A popular choice are \emph{de Bruijn indices},
\Fixme{Add some citations?}
where each variable is represented by a natural number,
counting the number of bindings between variable occurence and its binding:
$0$ refers to the innermost binding, $1$ to the next-innermost etc.

Still, there might be \emph{free variables},
where the de Bruijn index is larger than the number of bindings it has access to
(\emph{in scope}).
If this happens unexpectedly during evaluation, an error is raised.
Similarly, the type of a bound expression might not match the expected type at the variable occurence
where it is referenced.
This makes the evaluation function partial;
it should only be called after validating type- and scope-safety.
\Fixme{Show possible bugs in transformations}

When implementing a compiler in a dependently typed programming language,
one does not need to accept partiality and the need for human vigilance.
With \emph{intrinsically typed syntax trees}, type- and scope-safety invariants
are specified on the type level and verified by the type checker.
We will demonstrate the approach in Agda and start by defining the types that terms can have.
\Fixme{Too long-winded and detailed?}
\Fixme{Add some further structure to this subsection? Paragraphs?}

\begin{code}
  data U : Set where
    BOOL  : U
    NAT   : U

  interpret_ : U -> Set
  (interpret(BOOL)) = Bool
  (interpret(NAT))  = Nat
\end{code}

To know if a variable occurence is valid, one must consider its \emph{context},
the bindings that are in scope.
With de Bruijn indices in an untyped setting, it would suffice to know the number of bindings in scope.
In a typed setting, it is also necessary to know the type of each binding,
so I represent the context by a list of types: One for each binding in scope, from innermost to outermost.

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
\cite{allais2018universe}


\subsection{Well-founded Recursion}
\Fixme{Is this worth explaining here?}


\section{Preliminary Results}
\Draft{What examples can you handle already?}
\Draft{What prototype have I built?}
\Draft{How can I generalize these results? What problems have I identified or do I expect?}

As a first step, I implemented one optimisation in Agda,
including a mechanised proof of its preservation of semantics.
The main ideas are outlined below;
the full source code is available online
\footnote{\url{https://git.science.uu.nl/m.h.heinzel/correct-optimisations}}.


\subsection{Dead Binding Elimination}

% TODO: we->I
\paragraph{Sub-contexts}
To reason about the part of a context that is live (actually used),
we introduce \emph{sub-contexts}.
Conceptually, these are contexts that admit an
\emph{order-preserving embedding} (OPE) \cite{chapman2009type} into the original context,
and we capture this notion in a single data type.
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
  evalLive :
    LiveExpr Delta Delta' tau -> Env (floor(DeltaU)) -> (Irrelevant(Delta c= DeltaU)) -> (interpret(tau))
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
A binding that is removed can contain the only occurrences of some other variable.
This makes another binding dead, allowing further optimisation when running the algorithm again.
While in our simple setting all these bindings could be identified in a single pass
using \emph{strong live variable analysis},
in general it can be useful to simply iterate the optimisation until a fixpoint is reached.

Such an iteration is not structurally recursive, so Agda's termination checker needs our help.
We observe that the algorithm must terminate
since the number of bindings decreases with each iteration (but the last) and cannot become negative.
This corresponds to the ascending chain condition in program analysis literature
\cite{nielson1999analysis}.
To convince the termination checker, we use \emph{well-founded recursion} \cite{bove2016recursion}
on the number of bindings.

The correctness follows directly from the correctness of each individual iteration step.


\subsection{Observations}

One interesting observation is that the correctness proof does not rely on how
|analyse| computes the annotations.
At first, this does not seem particularly useful,
but for other optimisations the analysis might use complex, frequently changing heuristics to decide
which transformations are worth it.
\Fixme{Just a reused paragraph, expand!}


\section{Timetable and Planning}

\subsection{Further Work}
\Draft{What will I do with the remainder of my thesis?}
\Fixme{Initial draft, to be refined}

\paragraph{Extending the Language}
Since our language only contains let-bindings,
it might be of interest to extend it with $\lambda$-abstractions
(forming a simply-typed $\lambda$-calculus).
Some increase in complexity seems necessary to eliminate applications of
functions that do not use their argument,
but we hope that our work is still largely applicable.
The problem gets more challenging when introducing recursive bindings.
Conversely, adding sum and product types might require more extensive bookkeeping,
but should not pose fundamental difficulties.
\Fixme{extend, itemize}

\paragraph{Other Analyses}
There are several other binding-related transformations to explore,
such as moving bindings up or down in the syntax tree.
Another interesting type of optimisation is avoidance of redundant computations
using \emph{available expression analysis}.
An example is \emph{common subexpression elimination},
where subexpressions get replaced by variables bound to equivalent declarations
(pre-existing or newly created).
\Fixme{extend, itemize}

\paragraph{Generalisation}
Ideally, further exploration will lead to the discovery of common patterns
and useful strategies for performing optimisations on intrinsically typed syntax trees.
One possible avenue is the syntax-generic definition of operations and proofs.


\subsection{Schedule}
\Draft{Give an approximate estimation/timetable for what you will do and when you will be done.}

The thesis deadline is on 09.06.2023.
To allow for sufficient grading time,
I will submit my thesis until 26.05.2023, the end of week 21.

\vspace{1em}
\noindent
\setlength\tabcolsep{3pt}
\begin{tabularx}{\textwidth}{@@{}m{0.17\textwidth}||*{20}{L}}
  \textbf{Week}
    & \Week{2} & \Week{3} & \Week{4} & \Week{5} & \Week{6} & \Week{7} & \Week{8} & \Week{9} & \Week{10} & \Week{11} & \Week{12} & \Week{13} & \Week{14} & \Week{15} & \Week{16} & \Week{17} & \Week{18} & \Week{19} & \Week{20} & \Week{21} \\
  \hline
  Step 1
    & \X & \X & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  \\
  The rest
    & \  & \  & \X & \X & \X & \X & \X & \X & \X & \X & \X & \X & \X & \X & \X & \X & \X & \X & \  & \  \\
  Proofreading
    & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \  & \X & \X & \X \\
\end{tabularx}
\Fixme{Fill out!}


\bibliographystyle{acm}
\bibliography{../correct-optimisations}{}

\pagebreak
\appendix
\section{Ethics Quick Scan}
\Draft{(anonymised report)}
\Fixme{Insert!}

\end{document}
