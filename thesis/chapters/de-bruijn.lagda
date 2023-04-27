%include agda.fmt
%include custom.fmt

\chapter{de Bruijn Representation}
\label{ch:de-bruijn}
  Whether we use explicit names or de Bruijn indices,
  the language as seen so far makes it possible to represent expressions
  that are ill-typed (e.g. performing addition on Booleans)
  or accidentally open (containing free variables).
  Evaluating such an expression leads to a runtime error;
  the evaluation function is partial.

  When implementing a compiler in a dependently typed programming language,
  we can define \emph{intrinsically typed syntax trees} with de Bruijn indices,
  where type- and scope-correctness invariants are specified on the type level
  and verified by the type checker.
  \Fixme{mention inductive families (Dybjer)?}
  This allows for a total evaluation function
  \cite{Augustsson1999WellTypedInterpreter}.
  As a consequence, transformations on the syntax tree 
  only typecheck if they preserve the invariants.
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
      _=>_  : U
      BOOL  : U
      NAT   : U

    interpretU_ : U -> Set
    (interpretU(sigma => tau))  = (interpretU(sigma)) -> (interpretU(tau))
    (interpretU(BOOL))          = Bool
    (interpretU(NAT))           = Nat
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
      Var   : Ref sigma Gamma -> Expr sigma Gamma
      App   : Expr (sigma => tau) Gamma -> Expr sigma Gamma -> Expr tau Gamma
      Lam   : Expr tau (sigma :: Gamma) -> Expr (sigma => tau) Gamma
      Let   : Expr sigma Gamma -> Expr tau (tau :: Gamma) -> Expr tau Gamma
      Val   : (interpretU(sigma)) -> Expr sigma Gamma
      Plus  : Expr NAT Gamma -> Expr NAT Gamma -> Expr NAT Gamma
  \end{code}

  This allows the definition of a total evaluator
  using an environment that matches the expression's context.

  \begin{code}
    eval : Expr sigma Gamma -> Env Gamma -> (interpretU(sigma))
    eval (Var x)       env  = lookup x env
    eval (App e1 e2)   env  = eval e1 env (eval e2 env)
    eval (Lam e)       env  = lambda v -> eval e (Cons v env)
    eval (Let e1 e2)   env  = eval e2 (Cons (eval e1 env) env)
    eval (Val v)       env  = v
    eval (Plus e1 e2)  env  = eval e1 env + eval e2 env
  \end{code}


\section{Order-preserving Embeddings}
\Outline{
  We use \emph{order-preserving embedding} (OPE) \cite{Chapman2009TypeCheckingNormalisation}
  e.g. to reason about the part of a context that is live (actually used).
  Show definition, composition, laws.
  These can be used to specify operations on |Env|, |Ref|, |Expr| (which we also show).
  We can prove lemmas about how they relate,
  e.g. |eval (rename-Expr theta e) env == eval e (project-Env theta env)|.
}
\Fixme{terminology: OPE vs thinning?}
\Fixme{Have a separate chapter for Expr-independent operations on OPE, Ref, Env? (basically |Language.Core|)}


\section{Dead Binding Elimination}
\label{sec:de-bruijn-dbe}

\subsection{Direct Approach}
\label{sec:de-bruijn-dbe-direct}
\Outline{
  The transformation returns |Expr sigma ^^ Gamma|,
  indicating that only part of the context is used.

  For |Let|, note that using the live context of the transformed body
  automatically gives us the strong version.

  Also note that we need to rename at every binary operator
  We explain why this cannot be avoided with this approach.
  We somehow need to know upfront which context the expression should have in the end.
  This will be shown in the next section.

  We prove correctness (semantics-preservation).
}

\subsection{Using Live Variable Analysis}
\label{sec:de-bruijn-dbe-live}
  \paragraph{Liveness annotations}
  We can annotate each expression with its \emph{live variables},
  the context |Delta| that is really used and embeds into
  the original context with OPE such as |theta : Delta C= Gamma|.
  To that end, we define annotated expressions |LiveExpr tau theta|.

  \begin{code}
    data LiveExpr {Gamma : Ctx} : U -> {Delta : Ctx} -> Delta C= Gamma -> Set where
      Var :
        (x : Ref sigma Gamma) ->
        LiveExpr sigma (o-Ref x)
      App :
        {theta1 : Delta1 C= Gamma} {theta2 : Delta2 C= Gamma} ->
        LiveExpr (sigma => tau) theta1 ->
        LiveExpr sigma theta2 ->
        LiveExpr tau (theta1 ∪ theta2)
      Lam :
        {theta : Delta C= (sigma :: Gamma)} ->
        LiveExpr tau theta ->
        LiveExpr (sigma => tau) (pop theta)
  \end{code}
  \Outline{
    Explain for some constructors, e.g.
    for variables we start with a singleton context using |o-Ref|.
    Also make sure the necessary operations like |pop| and |\/| are introduced.
  }

  For |Let|, one way is to handle it using a combination of the operations for
  |App| and |Lam|.
  This corresponds to a non-strong live variable analysis,
  since even if the body is dead, we end up considering the declaration
  for the live context.
  \begin{code}
      Let :
        {theta1 : Delta1 C= Gamma} {theta2 : Delta2 C= (sigma :: Gamma)} ->
        LiveExpr sigma theta1 ->
        LiveExpr tau theta2 ->
        LiveExpr tau (theta1 ∪ pop theta2)
  \end{code}

  The other is to do strongly live variable analysis with a custom operation |combine|,
  which ignores the declaration's context if it is not used in the body.
  \begin{code}
    combine-domain : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> Ctx
    combine-domain {Delta2 = Delta2} theta1 (theta2 o') = Delta2
    combine-domain theta1 (theta2 os) = ∪-domain theta1 theta2

    combine : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> combine-domain theta1 theta2 C= Gamma
    combine theta1 (theta2 o') = theta2
    combine theta1 (theta2 os) = theta1 ∪ theta2
  \end{code}
  \begin{code}
      Let :
        {theta1 : Delta1 C= Gamma} {theta2 : Delta2 C= (sigma :: Gamma)} ->
        LiveExpr sigma theta1 ->
        LiveExpr tau theta2 ->
        LiveExpr tau (combine theta1 theta2)
  \end{code}

  We will use the latter version, but later show how to achieve the same result
  by iterating the non-strong version.

  \paragraph{Analysis}
  To create an annotated expressions, we need to perform
  some static analysis of our source programs.
  The function |analyse| computes an existentially qualified live context and OPE,
  together with a matching annotated expression.
  \begin{code}
    analyse : Expr tau (floor(Delta)) -> (Exists (Delta') (SubCtx Gamma)) LiveExpr Delta Delta' tau
  \end{code}

  It is sensible to assume that analysis does not change the expression,
  which we capture by stating that we can always forget the annotations
  to obtain the original expression (|forget . analyse == id|).
  \begin{code}
    forget : {theta : Delta C= Gamma} -> LiveExpr tau theta -> Expr tau Gamma

    analyse-preserves :
      (e : Expr tau Gamma) ->
      let _ , _ , le = analyse e
      in forget le == e
  \end{code}

  Note that we can evaluate |LiveExpr| directly, differing from |eval| mainly
  in the |Let|-case, where we match on |theta2| to distinguish whether the bound variable is live.
  If it is not, we directly evaluate the body, ignoring the bound declaration.
  Another important detail is that evaluation works under any environment containing (at least) the live context.

  \begin{code}
    evalLive : {theta : Delta C= Gamma} -> LiveExpr tau theta -> Env Gamma' -> Delta C= Gamma' -> (interpretU(tau))
    evalLive (Let {theta2 = theta2 o'} e1 e2) env theta' =
      evalLive e2 env theta' 
    (dots)
  \end{code}

  \paragraph{Transformation}
  The \emph{optimised semantics} above indicates that
  we can do a similar program transformation
  and will be useful in its correctness proof.
  The implementation simply maps each constructor to its counterpart in |Expr|,
  again distinguishing the cases for live and dead let-bindings.

  \begin{code}
    transform : {theta : Delta C= Gamma} -> LiveExpr tau theta -> Delta C= Gamma' -> Expr tau Gamma'
    transform (Let {theta2 = theta2 o'} e1 e2) theta' =
      transform e2 theta' 
    (dots)
  \end{code}

  As opposed to |forget|, which stays in the original context,
  here we remove unused variables, only keeping |Gamma'|.
  \Outline{
    We avoid renaming here, because we know the required context upfront
    and can pass it into the recursive call.
  }
  We can now compose analysis and transformation into an operation
  with the same signature as the direct implementation
  in section \ref{sec:de-bruijn-dbe-direct}.

  \begin{code}
    dbe : Expr sigma Gamma -> Expr sigma ^^ Gamma
    dbe e = let _ , theta , le = analyse e in transform le oi ^ theta
  \end{code}

  \paragraph{Correctness}
  We want to show that dead binding elimination preserves semantics,
  which we can conceptually express as
  |eval . dbe == eval|.
  % |eval . transform . analyse == eval|.
  For that, it is sufficient to show the following:

  \begin{code}
    eval . transform == eval . forget
  \end{code}

  We can then pre-compose |analyse| on both sides and remove
  |forget . analyse| (which we know forms an identity)
  to obtain the desired |eval . transform . analyse == eval|.
  The proof gets simpler if we split it up using the optimised semantics:

  \begin{code}
    evalLive == eval . transform
    evalLive == eval . forget
  \end{code}

  The actual proof statements in Agda are more involved,
  since they quantify over the expression and environment used for evaluation.
  As foreshadowed in the definition of |evalLive|, the statements are also generalised
  to evaluation under any |Env Gamma'|,
  as long as it contains the live context.
  This gives us more flexibility when using the inductive hypothesis.
  \Fixme{show exact proof statements}

  Both proofs work inductively on the expression, with most cases being a straight-forward congruence.
  The interesting one is again |Let|, where we split cases on the variable being used or not
  and need some auxiliary facts about evaluation, renaming and contexts.

  \paragraph{Iterating the Optimisation}
  As discussed in section \ref{ch:program-transformations},
  more than one pass of dead binding elimination might be necessary to remove all unused bindings.
  While in our simple setting all these bindings could be identified in a single pass
  using strongly live variable analysis,
  in general it can be useful to simply iterate optimisations until a fixpoint is reached.

  Consequently, we keep applying |dbe| as long as the number of bindings decreases.
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


\section{Let-sinking}
\label{sec:de-bruijn-let-sinking}
\Draft{
  We want to push a let-binding as far inward as possible,
  without pushing into a $\lambda$-abstraction or duplicating the binding.
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
  Once we stop pushing the let-binding (e.g. when we reach a $\lambda$-abstraction),
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
Doing it for let-sinking caused issues.
Could co-de-Bruijn give us the same benefits by default?
It would also help with CSE (equality of terms).
}
