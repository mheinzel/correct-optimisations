%include agda.fmt
%include custom.fmt

\chapter{de Bruijn Representation}
\label{ch:de-bruijn}

Whether we use explicit names or de Bruijn indices,
the language as seen so far makes it possible to represent expressions
that are ill-typed (e.g. adding Booleans)
or accidentally open (containing free variables).
Evaluating such an expression leads to a runtime error;
the evaluation function is partial.

When implementing a compiler in a dependently typed programming language,
we can define \emph{intrinsically typed syntax trees} with de Bruijn indices,
where type- and scope-correctness invariants are specified on the type level
and verified by the type checker.
\Fixme{mention inductive families (Dybjer)?}
This makes the evaluation function total
\cite{Augustsson1999WellTypedInterpreter}.
Similarly, transformations on the syntax tree need to preserve the invariants.
While the semantics of the expression could still change,
guaranteeing type- and scope-correctness rules out
a large class of mistakes.

\section{Intrinsically Typed Syntax}
\label{sec:de-bruijn-intrinsically-typed}

To demonstrate this approach in Agda, 
let us start by defining the types that expressions can have.
\Fixme{rename to \emph{sorts}?}

\begin{code}
  data U : Set where
    BOOL  : U
    NAT   : U

  interpretU_ : U -> Set
  (interpretU(BOOL))  = Bool
  (interpretU(NAT))   = Nat
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
    Cons  : (interpretU(sigma)) -> Env Gamma -> Env (sigma :: Gamma)
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
  lookup : Ref sigma Gamma -> Env Gamma -> (interpretU(sigma))
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
  data Expr : (Gamma : Ctx) (tau : U) -> Set where
    Val   : (interpretU(sigma)) -> Expr sigma Gamma
    Plus  : Expr NAT Gamma -> Expr NAT Gamma -> Expr NAT Gamma
    Let   : Expr sigma Gamma -> Expr tau (tau :: Gamma) -> Expr tau Gamma
    Var   : Ref sigma Gamma -> Expr sigma Gamma
\end{code}
\Fixme{Add |Lam|!}

This allows the definition of a total evaluator
using an environment that matches the expression's context.

\begin{code}
  eval : Expr sigma Gamma -> Env Gamma -> (interpretU(sigma))
  eval (Val v)       env  = v
  eval (Plus e1 e2)  env  = eval e1 env + eval e2 env
  eval (Let e1 e2)   env  = eval e2 (Cons (eval e1 env) env)
  eval (Var x)       env  = lookup x env
\end{code}

\section{Dead Binding Elimination}
\label{sec:de-bruijn-dbe}

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
|Expr tau (floor(Delta))| in some sub-context.
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
  analyse : Expr tau (floor(Delta)) -> (Exists (Delta') (SubCtx Gamma)) LiveExpr Delta Delta' tau
  forget  : LiveExpr Delta Delta' tau -> Expr tau (floor(Delta))
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
  evalLive : LiveExpr Delta Delta' tau -> Env (floor(DeltaU)) -> (Irrelevant(Delta c= DeltaU)) -> (interpretU(tau))
\end{code}

This \emph{optimised semantics} shows that we can do a similar program transformation
and will be useful in its correctness proof.
The implementation simply maps each constructor to its counterpart in |Expr|,
with some renaming
(e.g. from |(floor(Delta1))| to |(floor(Delta1 \/ Delta2)|)
and the abovementioned case distinction.

\begin{code}
  dbe : LiveExpr Delta Delta' tau -> Expr tau (floor(Delta'))
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
As discussed in section \ref{ch:program-transformations},
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

\section{Strong Dead Binding Elimination}
\label{sec:de-bruijn-dbe-strong}
\Question{Merge this into previous section? Or, since strong version is so similar, do that immediately?}
\Draft{
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
}

\section{Let-floating}
\label{sec:de-bruijn-let-floating}
\Draft{
  We want to push a let-binding as far inward as possible,
  without pushing into a $lambda$-abstraction or duplicating the binding.
  This seemingly simple transformation shows some unexpected complications.
  \paragraph{Signature}
  While we initially deal with a binding for the topmost entry in the context
  (|Expr sigma Gamma -> Expr tau (sigma :: Gamma) -> Expr tau Gamma|),
  recursively applying this function under binders requires more flexibility.
  The solution chosen here allows the position of that binding to be specified
  by a reference.
  \begin{code}
  pop-at : (Gamma : Ctx) -> Ref tau Gamma -> Ctx
  pop-at (sigma :: Gamma) Top = Gamma
  pop-at (sigma :: Gamma) (Pop i) = sigma :: pop-at Gamma i
  \end{code}
  \begin{code}
  push-let : (i : Ref sigma Gamma) -> Expr sigma (pop-at Gamma i) -> Expr tau Gamma -> Expr tau (pop-at Gamma i)
  \end{code}
  Supplying |Top| as the first argument results in the same signature
  as the |Let| constructor itself.
  Note that we could have alternatively used list concatenation or insertion, e.g.
  \begin{code}
  Expr sigma (pop-at Gamma i)    -> Expr tau Gamma                        -> Expr tau (pop-at Gamma i)
  Expr sigma (Gamma1 ++ Gamma2)  -> Expr tau (Gamma1 ++ sigma :: Gamma2)  -> Expr tau (Gamma1 ++ Gamma2)
  Expr sigma Gamma               -> Expr tau (insert n sigma Gamma)       -> Expr tau Gamma
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
  Once we stop pushing the let-binding (e.g. when we reach a $lambda$-abstraction),
  it is still necessary to rename the expression in its body,
  since it makes use of the newly created binding,
  but expects it at a different de Bruijn index.
  \begin{code}
  rename-top : (i : Ref sigma Gamma) -> Expr tau Gamma -> Expr tau (sigma :: pop-at Gamma i)
  \end{code}
  \paragraph{Binary constructors}
  For binary operators, we need to check which subexpressions make use of the declaration.
  Instead of working with an annotated version of the syntax tree,
  we here query variable usage in subexpressions on demand.
  If the binding is not used in a subexpression,
  we need to obtain a strengthened version of that expression,
  so we combine this into a single operation.
  \begin{code}
    strengthen-pop-at : (i : Ref sigma Gamma) -> Expr tau Gamma -> Maybe (Expr tau (pop-at Gamma i))
  \end{code}
  \OpenEnd{
  Repeated querying is not ideal. This problem goes away with co-de-Bruijn representation,
  but could it also be avoided here using annotations (as with |LiveExpr|)
  or carrying additional information bottom-up?
  }
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
  \paragraph{Correctness}
}
\OpenEnd{No correctness proof yet, how hard is it?}

\section{Discussion}
\label{sec:de-bruijn-discussion}
\Outline{
Usage information is nice, but complicated to maintain.
Doing it for let-floating caused issues.
Could co-de-Bruijn give us the same benefits by default?
It would also help with CSE (equality of terms).
}
