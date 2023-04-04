\documentclass{report}

% workaround, see https://github.com/kosmikus/lhs2tex/issues/82
\let\Bbbk\undefined

%include agda.fmt
%include custom.fmt

\include{preamble}


\begin{document}

\include{title}

\tableofcontents


\chapter{Overview of Current Results}

\section{De Bruijn Representation}
\subsection{Syntax Tree}
  Using standard intrinsically-typed syntax trees.
  \begin{code}
    data Expr (Gamma : Ctx) (tau : U) -> Set where
      Val   : (interpret(sigma)) -> Expr Gamma sigma
      Plus  : Expr Gamma NAT -> Expr Gamma NAT -> Expr Gamma NAT
      Let   : Expr Gamma sigma -> Expr (sigma :: Gamma) tau -> Expr Gamma tau
      Var   : Ref sigma Gamma -> Expr Gamma sigma
  \end{code}
  Here, the context of variables in scope is a list of types,
  references are de Bruijn indices into that list
  and the environment for evaluation is a list of values matching the context.
  \begin{code}
    data Ref (sigma : U) : Ctx -> Set where
      Top  : Ref sigma (sigma :: Gamma)
      Pop  : Ref sigma Gamma -> Ref sigma (tau :: Gamma)
  \end{code}
  \begin{code}
    data Env : Ctx -> Set where
      Nil   : Env []
      Cons  : (interpret(sigma)) -> Env Gamma -> Env (sigma :: Gamma)
  \end{code}
  \begin{code}
    lookup : Ref sigma Gamma -> Env Gamma -> (interpret(sigma))
    lookup Top      (Cons v env)   = v
    lookup (Pop i)  (Cons v env)   = lookup i env
  \end{code}
  \begin{code}
    eval : Expr Gamma sigma -> Env Gamma -> (interpret(sigma))
    eval (Val v)       env  = v
    eval (Plus e1 e2)  env  = eval e1 env + eval e2 env
    eval (Let e1 e2)   env  = eval e2 (Cons (eval e1 env) env)
    eval (Var x)       env  = lookup x env
  \end{code}
  For more details, see section \ref{sec:background-intrinsically-typed}.
\subsection{Dead Binding Elimination}
  \paragraph{Analysis}
  In a first pass, we perform \emph{live variable analysis}
  and create an annotated expression using \emph{sub-contexts}.
  \begin{code}
    data SubCtx : Ctx -> Set where
      Empty  : SubCtx []
      Drop   : SubCtx Gamma -> SubCtx (tau :: Gamma)
      Keep   : SubCtx Gamma -> SubCtx (tau :: Gamma)
  \end{code}
  \begin{code}
    floor_ : SubCtx Gamma -> Ctx
  \end{code}
  \begin{code}
    data LiveExpr : (Delta Delta' : SubCtx Gamma) (tau : U) -> Set where
      Let : LiveExpr Delta Delta1 sigma ->
            LiveExpr (Keep Delta) Delta2 tau ->
            LiveExpr Delta (Delta2 \/ pop Delta2) tau
      (dots)
  \end{code}
  \begin{code}
    analyse : Expr (floor(Delta)) tau -> (Exists (Delta') (SubCtx Gamma)) LiveExpr Delta Delta' tau
  \end{code}
  \paragraph{Transformation}
  In a second pass, dead let-bindings can then be identified and removed.
  \begin{code}
    dbe : LiveExpr Delta Delta' tau -> Expr (floor(Delta')) tau
  \end{code}
  \paragraph{Correctness}
  We show that the transformation preserves semantics based on the (total) evaluation function.
  \paragraph{Iterating the transformation}
  Since this transformation can require multiple runs to eliminate all possible bindings
  (section \ref{sec:background-transformations}),
  we use well-founded recursion to iterate it until a fixpoint is reached.
  \paragraph{}
  For more details, see section \autoref{sec:results-dbe}.
\subsection{Strong Dead Binding Elimination}
  To avoid the need for iterating the transformation,
  we employ the more precise \emph{strongly live variable analysis}.
  The main difference is that we only consider variable usages in a declaration
  if that declaration itself is live.
  \begin{code}
    combine : SubCtx Gamma -> SubCtx (sigma :: Gamma) -> SubCtx Gamma
    combine Delta1 (Drop Delta2) = Delta2
    combine Delta1 (Keep Delta2) = Delta1 \/ Delta2
  \end{code}
  \begin{code}
    data LiveExpr : (Delta Delta' : SubCtx Gamma) (tau : U) -> Set where
      Let : LiveExpr Delta Delta1 sigma ->
            LiveExpr (Keep Delta) Delta2 tau ->
            LiveExpr Delta (Delta2 \/ pop Delta2) tau
      (dots)
  \end{code}
  The remaining algorithm and most of the correctness proof are unaffected.
\subsection{Pushing Bindings Inward}
  We want to push a let-binding as far inward as possible,
  without pushing into a lambda or duplicating the binding.
  This seemingly simple transformation shows some unexpected complications.
  \paragraph{Signature}
  While we initially deal with a binding for the topmost entry in the context
  (|Expr Gamma sigma -> Expr (sigma :: Gamma) tau -> Expr Gamma tau|),
  recursively applying this function under binders requires more flexibility.
  The solution chosen here allows the position of that binding to be specified
  by a reference.
  \begin{code}
  pop-at : (Gamma : Ctx) -> Ref tau Gamma -> Ctx
  pop-at (sigma :: Gamma) Top = Gamma
  pop-at (sigma :: Gamma) (Pop i) = sigma :: pop-at Gamma i
  \end{code}
  \begin{code}
  push-let : (i : Ref sigma Gamma) -> Expr (pop-at Gamma i) sigma -> Expr Gamma tau -> Expr (pop-at Gamma i) tau
  \end{code}
  Supplying |Top| as the first argument results in the same signature
  as the |Let| constructor itself.
  Note that we could have alternatively used list concatenation or insertion, e.g.
  \begin{code}
  Expr (pop-at Gamma i) sigma    -> Expr Gamma tau                        -> Expr (pop-at Gamma i) tau
  Expr (Gamma1 ++ Gamma2) sigma  -> Expr (Gamma1 ++ sigma :: Gamma2) tau  -> Expr (Gamma1 ++ Gamma2) tau
  Expr Gamma sigma               -> Expr (insert n sigma Gamma) tau       -> Expr Gamma tau
  \end{code}
  \paragraph{Variables}
  When pushing a binding into a variable, there are two possible cases:
  If variable references exactly the let-binding we are pushing,
    we can replace it by the declaration,
    effectively inlining it.
  If the variable it references a different element of the context,
    the declaration is eliminated
    and we  only need to strengthen the variable into the smaller context.
  \paragraph{Creating the binding}
  Once we stop pushing the let-binding (e.g. when we reach a lambda),
  it is still necessary to rename the expression in its body,
  since it makes use of the newly created binding,
  but expects it at a different de Bruijn index.
  \begin{code}
  rename-top : (i : Ref sigma Gamma) -> Expr Gamma tau -> Expr (sigma :: pop-at Gamma i) tau
  \end{code}
  \paragraph{Binary constructors}
  For binary operators, we need to check which subexpressions make use of the declaration.
  Instead of working with an annotated version of the syntax tree,
  we here query variable usage in subexpressions on demand.
  If the binding is not used in a subexpression,
  we need to obtain a strengthened version of that expression,
  so we combine this into a single operation.
  \begin{code}
    strengthen-pop-at : (i : Ref sigma Gamma) -> Expr Gamma tau -> Maybe (Expr (pop-at Gamma i) tau)
  \end{code}
  If one of the subexpressions can be strengthened, we only need to recurse into the other.
  If both subexpressions use the declaration, we do not push further,
  but create a let-binding at the current location (see above).
  \paragraph{Binders}
  If we recurse into the body of a let-binding,
  an additional binding comes into scope.
  This means that we need to bump the reference
  and weaken the declaration.
  \begin{code}
    weaken : Expr tau Gamma -> Expr tau (sigma :: Gamma)
  \end{code}
\subsection{Open Ends and Questions}
  \begin{itemize}
    \item review dead binding elimination: after gaining additional experience,
      are annotated expressions with sub-contexts still a good design?
    \item dead binding elimination: since the stronger version is so similar,
      do that immediately?
    \item push let inward: repeated querying is not ideal,
      but there were complications with |LiveExpr|.
    \item push let inward: no correctness proof yet
  \end{itemize}

\section{Co-de-Bruijn Representation}
\subsection{Syntax Tree}
  We follow McBride's work on co-de-Bruijn representation
  \cite{McBride2018EveryBodysGotToBeSomewhere}
  and use OPEs |_C=_| to define the type of relevant pairs |_><R_|
  where each variable in the context must be in the context of one of the two subexpressions,
  as well as bound variables |_||-_|.
  \begin{code}
    data Expr : (sigma : U) (Gamma : Ctx) -> Set where
      Var : Expr sigma (sigma :: [])
      App : (Expr (sigma ⇒ tau) ><R Expr sigma) Gamma -> Expr tau Gamma
      Lam : ((sigma :: []) |- Expr tau) Gamma -> Expr (sigma ⇒ tau) Gamma
      Let : (Expr sigma ><R ((sigma :: []) |- Expr tau)) Gamma -> Expr tau Gamma
      Val : (v : (interpret (sigma))) -> Expr sigma []
      Plus : (Expr NAT ><R Expr NAT) Gamma -> Expr NAT Gamma
  \end{code}
\subsection{Conversion to de Bruijn Representation}
  The main difference here is that
  variables are not kept in the context until the latest,
  but discarded at the earliest opportunity.
  More concretely,
  in de Bruijn representation, subexpressions keep the full context of available bindings,
  while in co-de-Bruijn representation an OPE selects the subset that occurs.
  A converted expression will therefore generally be required to have a larger context than before,
  indicated by an OPE.
  \begin{code}
    from :  Gamma' C= Gamma -> Expr sigma Gamma' -> DeBruijn.Expr Gamma sigma
  \end{code}
  The implementation proceeds by induction over the syntax,
  composes OPEs on the way
  and finally at the variable makes use of the fact
  that an OPE from a singleton list is isomorphic to a de Bruijn reference.
  The proof of semantic equivalence mainly consists of congruences.
\subsection{Conversion from de Bruijn Representation}
  In the opposite direction,
  the resulting co-de-Bruijn expression will generally have a smaller context
  that is not known upfront.
  This can be expressed conveniently by returning an expression together with an OPE
  into the original context.
  \begin{code}
    record _^^_ (T : List I -> Set) (scope : List I) : Set where
      constructor _^_
      field
        {support} : List I
        thing : T support
        thinning : support C= scope
  \end{code}
  \begin{code}
    into : DeBruijn.Expr Gamma sigma -> Expr sigma ^^ Gamma
  \end{code}
\subsection{Dead Binding Elimination}
  Co-de-Bruijn expressions enforce that every variable in an expression's context
  must occur somewhere.
  However, there can still be dead bindings:
  The declaration of type |tau| bound by |tau :: [] ||- e| does not need to appear in the context of |e|.
  It can be immediately discarded, making the binding dead.
  We need to identify such let-bindings and eliminate them.
  Due to the variable usage information already maintained within co-de-Bruijn expressions,
  no further analysis is necessary.
  \begin{code}
    dbe : Expr tau Gamma -> Expr tau ^^ Gamma
    dbe (Let (pairR (e1 ^ phi1) ((oz o' \\ e2) ^ phi2) c)) =
      thin^^ phi2 (dbe e2)
    dbe (Let (pairR (e1 ^ phi1) ((oz os \\ e2) ^ phi2) c)) =
      map^^ Let (thin^^ phi1 (dbe e1) ,R thin^^ phi2 ((_ :: []) \\R dbe e2))
    (dots)
  \end{code}
  Since the body is generally in a smaller context than the whole let-binding was,
  we again need to return an expression with a thinning.
  This has several consequences:
  Firstly, these new thinnings need to be composed with the existing ones
  on the way up (e.g. using |thin^^|).
  Secondly, we need to rediscover the variable usage information,
  i.e. calculate new contexts and covers at each node using |_\\R_| and |_,R_|.
  And finally, this also means that (as in the de Bruijn setting)
  previously live bindings might now have become dead,
  requiring another iteration.
\subsection{Strong Dead Binding Elimination}
  To avoid this,
  instead of identifying unused bound variables in the input expression,
  we can do the recursive call \emph{first} and check whether the variable is used
  \emph{afterwards}.
  \Fixme{unexplained operations, hard to follow}
  \begin{code}
    let-? : (Expr sigma ><R ((sigma :: []) |- Expr tau)) Gamma -> Expr tau ^^ Gamma
    let-?     (pairR _ ((oz o' \\ e2)  ^ theta2)  _) = e2 ^ theta2
    let-? p@  (pairR _ ((oz os \\ _)   ^ _)       _) = Let p ^ oi
  \end{code}
  \begin{code}
    dbe : Expr tau Gamma -> Expr tau ^^ Gamma
    dbe (Let (pairR (e1 ^ phi1) ((_\\_ {bound = Gamma'} psi e2) ^ phi2) c)) =
      mult^^ (map^^ let-?
        (thin^^ phi1 (dbe e1) ,R thin^^ phi2 (map^^ (map|- psi) (Gamma' \\R dbe e2))))
    (dots)
  \end{code}
  The other cases are just the same as in the previous section.
  \paragraph{Correctness}
  We also prove that |dbe| preserves semantics.
  \begin{code}
    dbe-correct :
      (e : Expr tau Gamma') (env : Env Gamma) (theta : Gamma' C= Gamma) →
      let e' ^ theta' = dbe e
      in eval e' (theta' .. theta) env == eval e theta env
  \end{code}
  Even the more straight-forward cases require some massaging to get to work.
  For relevant pairs,
  we need to make use of associativity of |_.._| to apply some
  equalities about the result of |_,R_|.
  For bound variables,
  to even be able to apply the induction hypothesis,
  we need to make available some equalities about |_\\R_|.
  It then remains to use that composition and concatenation of OPEs commute:
  | (theta1 .. theta2) ++C= (phi1 .. phi2) == (theta1 ++C= phi1) .. (theta2 ++C= phi2) |.
  \\
  For let-bindings, we additionally use the semantics-preserving nature of |let-?|.
  \begin{code}
    lemma-let-? :
      (p : (Expr sigma ><R ((sigma :: []) |- Expr tau)) Gamma') (env : Env Gamma) (theta : Gamma' C= Gamma) ->
      let e' ^ theta' = let-? p
      in eval (Let p) theta env ≡ eval e' (theta' .. theta) env
  \end{code}
\subsection{Pushing Bindings Inward}
  The main differences compared to the de-Bruijn-based implementation are that
  \begin{itemize}
    \item variable usage information is available without querying it repeatedly,
    \item we can enforce that pushed declaration is used,
    \item the changes in context (and thus OPEs and covers) require laborious bookkeeping.
  \end{itemize}
  \paragraph{Signature}
  Since there are many properties and operations for OPEs and covers
  related to concatenation of contexts,
  we phrase the reordering of context differently than before:
  Instead of using a |Ref| to specify a particular binding in the context we want to move,
  we segment the context into a part before and after that binding.
  In de Bruijn setting, this would correspond to the following signature:
  \begin{code}
    push-let :
      (Gamma1 Gamma2 : Ctx) ->
      Expr sigma (Gamma1 ++ Gamma2) ->
      Expr tau (Gamma1 ++ sigma :: Gamma2) ->
      Expr tau (Gamma1 ++ Gamma2)
  \end{code}
  But here, declaration and binding form a relevant pair,
  each in their own context with an OPE into the overall context.
  \begin{code}
    push-let :
      (Gamma1 Gamma2 : Ctx) ->
      (decl : Expr sigma ^^ (Gamma1 ++ Gamma2)) ->
      (body : Expr tau ^^ (Gamma1 ++ sigma :: Gamma2)) ->
      Cover (thinning decl) (thinning body) ->
      Expr tau (Gamma1 ++ Gamma2)
  \end{code}
  For now, we will ignore the cover and also return the result with a thinning
  (i.e. without having to show that the whole context |Gamma1 ++ Gamma2| is relevant).
  \begin{code}
    push-let :
      (Gamma1 Gamma2 : Ctx) ->
      Expr sigma ^^ (Gamma1 ++ Gamma2) ->
      Expr tau ^^ (Gamma1 ++ sigma :: Gamma2) ->
      Expr tau ^^ (Gamma1 ++ Gamma2)
  \end{code}
  Finally, this representation is not as precise as it could be:
  The context of the body is thinned into a precisely specified overall context,
  but its on structure is opaque and needs to be discovered.
  For example, it does not need to make use of |sigma| and treating this case separately
  is cumbersome.
  Also, it is clear that the inner context consists of two parts
  (thinned into |Gamma1| and |Gamma2| respectively), but we first need to split it.
  We therefore make stronger assumptions about the context of the body
  (not just the context it is thinned into).
  The structure of the overall context, on the other hand is less important to us.
  \begin{code}
    push-let :
      (Gamma1 Gamma2 : Ctx) ->
      Expr sigma ^^ Gamma ->
      Expr tau (Gamma1 ++ sigma :: Gamma2) ->
      Gamma1 ++ Gamma2 C= Gamma ->
      Expr tau ^^ Gamma
  \end{code}

  \paragraph{Variables}
  Here we know that we are in a context consisting of exactly the type of the variable.
  After making this fact obvious to the typechecker,
  we can replace the variable by the declaration.
  \paragraph{Creating the binding}
  As in the de Bruijn setting, we need to rename the body of the newly created binding.
  However, it becomes more cumbersome here.
  \begin{code}
    reorder-Ctx :
      Expr tau Gamma -> (Gamma == Gamma1 ++ Gamma2 ++ Gamma3 ++ Gamma4) ->
      Expr tau (Gamma1 ++ Gamma3 ++ Gamma2 ++ Gamma4)
  \end{code}
  The context is split into four segments.
  Since subexpressions are in their own context,
  we first need to split their context (and the thinnings) into segments as well.
  This is also true for the cover, which needs to be carefully reassembled.
  Going under binders requires rewriting using list concatenation's associativity.
  \paragraph{Binary operators}
  Variable usage information is immediately available:
  We need to split and examine the thinnings of the subexpressions.
  \paragraph{Binders}
  % TODO: revisit why this requires so much massaging

  \paragraph{Correctness}
  Work in progress, but it's messy.
  There are many lemmas about splitting OPEs, reordering the context etc.
  It seems like some of the complications could be avoided
  if we manage to avoid the usage of |_,R_| as explained in the next paragraph.
  \paragraph{Covers}
  As hinted at above, it should not be necessary to return a result with a thinning.
  If all variables occur in either declaration or body, they will still occur in the result.
  This would also simplify the implementation (and thus the proof),
  since constructing a relevant pair directly is a simpler operation
  than using |_,R_| to discover a coproduct with new thinnings.
  However, constructing the required covers from the input requires non-trivial manipulation
  (splitting, composition, concatenation) and observing some equalities.
  It seems like the ``right'' way of doing things,
  but still requires some work.
% TODO: turn open ends into inline comments/todos?
\subsection{Open Ends}
  \begin{itemize}
    \item Dead Binding Elimination: adapt correctness proof from strong version
    \item Pushing Bindings Inward: can we avoid returning a thinning from push-let by manipulating the cover in a smart way?
    \item Pushing Bindings Inward: finish correctness proof
  \end{itemize}

\section{Generic de Bruijn Representation}
\subsection{Syntax Tree}
\subsection{Conversion to de Bruijn Representation}
\subsection{Open Ends}
(Dead Binding Elimination)

\section{Generic co-de-Bruijn Representation}
\subsection{Generic co-de-Bruijn Terms}
\subsection{Generic Semantics}
\subsection{Syntax Tree}
\subsection{Conversion to co-de-Bruijn Representation}
\subsection{Generic Conversion to de Bruijn Representation}
\subsection{Open Ends}
(Dead Binding Elimination)
(Strong Dead Binding Elimination)


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

\begin{enumerate}
  \item collect and document program analyses and transformations that can be performed on simple expression languages with variable binders
  \item implement several of these transformations using intrinsically typed expressions in the dependently-typed programming language Agda
  \item provide machine-checked proofs of the correctness (preservation of semantics) of the implemented transformations
  \item attempt to apply relevant techniques from the literature, such as datatype-generic programming on syntax trees
  \item identify common patterns and try capturing them as reusable building blocks (e.g. as datatype-generic constructions)
\end{enumerate}

The Ethics and Privacy Quick Scan of the Utrecht University Research Institute of Information and Computing Sciences was conducted (see Appendix \ref{app:ethics-quick-scan}).
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
  &\Let{x} 42 \In            \\
  &\ \ \Let{y} x + 6 \In     \\
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
  &\LetB 42 \In                       \\
  &\ \ \LetB \DeBruijn{0} + 6 \In     \\
  &\ \ \ \ \LetB \DeBruijn{0} + 7 \In \\
  &\ \ \ \ \ \ \DeBruijn{2}
\end{align*}

This makes $\alpha$-equivalence of expressions trivial and avoids variable capture,
but there are still opportunities for mistakes during transformations.
Adding or removing a binding
requires us to add or subtract 1 from all free variables in the binding's body.
We can see this in our example when removing the innermost (unused) let-binding:

\begin{align*}
  &\LetB 42 \In                   \\
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
\label{sec:background-intrinsically-typed}

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
    Drop   : SubCtx Gamma -> SubCtx (tau :: Gamma)
    Keep   : SubCtx Gamma -> SubCtx (tau :: Gamma)
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
  analyse : Expr (floor(Delta)) tau -> (Exists (Delta') (SubCtx Gamma)) LiveExpr Delta Delta' tau
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
As discussed in section \ref{sec:background-transformations},
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


\bibliography{../correct-optimisations}{}


\appendix
\includepdf[pages=1,offset=0cm -2.5cm,scale=0.55,pagecommand=\chapter{Ethics Quick Scan}\label{app:ethics-quick-scan}]{ethics-privacy-quick-scan-results-anonymised.pdf}
\includepdf[pages=2-,scale=0.55,pagecommand=\thispagestyle{plain}]{ethics-privacy-quick-scan-results-anonymised.pdf}

\end{document}
