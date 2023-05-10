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
  To demonstrate this approach in Agda \cite{Norell2008Agda},
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

  To know if a variable occurrence is valid, one must consider its \emph{context},
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

  A variable occurrence then is an index into its context,
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
      Let   : Expr sigma Gamma -> Expr tau (sigma :: Gamma) -> Expr tau Gamma
      Val   : (interpretU(sigma)) -> Expr sigma Gamma
      Plus  : Expr NAT Gamma -> Expr NAT Gamma -> Expr NAT Gamma
  \end{code}

  This allows the definition of a total evaluator
  using an environment that matches the expression's context.

  \begin{code}
    eval : Expr sigma Gamma -> Env Gamma -> (interpretU(sigma))
    eval (Var x)       env  = lookup x env
    eval (App e1 e2)   env  = eval e1 env (eval e2 env)
    eval (Lam e1)      env  = lambda v -> eval e1 (Cons v env)
    eval (Let e1 e2)   env  = eval e2 (Cons (eval e1 env) env)
    eval (Val v)       env  = v
    eval (Plus e1 e2)  env  = eval e1 env + eval e2 env
  \end{code}


\section{Thinnings}
  We use \emph{thinnings}, also called \emph{order-preserving embeddings} (OPE)
  \cite{Chapman2009TypeCheckingNormalisation},
  e.g. to reason about the part of a context that is live (actually used).
  We closely follow the syntactic conventions of McBride
  \cite{McBride2018EveryBodysGotToBeSomewhere},
  but grow our lists towards the left
  instead of using backwards lists and postfix operators.
  \begin{code}
    data _C=_ {I : Set} : List I -> List I -> Set where
      o' : Delta C= Gamma ->          Delta   C= (tau :: Gamma)
      os : Delta C= Gamma -> (tau ::  Delta)  C= (tau :: Gamma)
      oz : [] C= []
  \end{code}
  \Fixme{explain the intuition a bit?}
  \paragraph{Identity and composition}
  As an example of how we can construct thinnings,
  we can embed a context into itself (identity thinning)
  or embed the empty context into any other (empty thinning).
  \Fixme{Move |oe| directly into section \ref{sec:de-bruijn-dbe-liveness}?}
  \begin{code}
    oi : Gamma C= Gamma
    oi {Gamma = []} = oz
    oi {Gamma = _ :: _} = os oi

    oe : [] C= Gamma
    oe {Gamma = []} = oz
    oe {Gamma = _ :: _} = o' oe
  \end{code}
  Crucially, thinnings can be composed in sequence, and follow the expected laws.
  \begin{code}
    _.._ : Gamma1 C= Gamma2 -> Gamma2 C= Gamma3 -> Gamma1 C= Gamma3
    theta     .. o' phi  = o' (theta .. phi)
    o' theta  .. os phi  = o' (theta .. phi)
    os theta  .. os phi  = os (theta .. phi)
    oz        .. oz      = oz
  \end{code}
  \begin{code}
    law-..oi  :  (theta : Delta C= Gamma) -> theta .. oi == theta
    law-oi..  :  (theta : Delta C= Gamma) -> oi .. theta == theta
    law-....  :  (theta : Gamma1 C= Gamma2) (phi : Gamma2 C= Gamma3) (psi : Gamma3 C= Gamma4) ->
                 theta .. (phi .. psi) == (theta .. phi) .. psi
  \end{code}
  \Fixme{Rendering of names could be prettier.}
  \paragraph{Concatenating thinnings}
  Thinnings cannot just be composed in sequence, but also concatenated.
  \begin{code}
    _++C=_ : Delta1 C= Gamma1 -> Delta2 C= Gamma2 -> (Delta1 ++ Delta2) C= (Gamma1 ++ Gamma2)
    o' theta  ++C= phi = o'  (theta ++C= phi)
    os theta  ++C= phi = os  (theta ++C= phi)
    oz        ++C= phi = phi
  \end{code}
  This commutes nicely, i.e. 
  |(theta1 .. theta2) ++C= (phi1 .. phi2) == (theta1 ++C= phi1) .. (theta2 ++C= phi2)|
  \paragraph{Splitting thinnings}
  If we have a thinning into a concatenated context,
  we can also split the thinning itself accordingly.
  \Fixme{Is this the best place? Only needed for let-sinking.}
  \begin{code}
    record Split (Gamma1 : List I) (psi : Delta C= (Gamma1 ++ Gamma2)) : Set where
      constructor split
      field
        {used1} : List I
        {used2} : List I
        thinning1 : (used1 C= Gamma1)
        thinning2 : (used2 C= Gamma2)
        eq : Sigma (Delta == used1 ++ used2) lambda { refl -> psi == thinning1 ++C= thinning2 }
  \end{code}
  \begin{code}
    _-|_ : (Gamma1 : List I) (psi : Delta C= (Gamma1 ++ Gamma2)) -> Split Gamma1 psi
    []               -| psi                                                    = split oz psi (refl , refl)
    (tau :: Gamma1)  -| o' psi                with Gamma1 -| psi
    (tau :: Gamma1)  -| o' .(phi1 ++C= phi2)  | split phi1 phi2 (refl , refl)  = split (o' phi1) phi2 (refl , refl)
    (tau :: Gamma1)  -| os psi                with Gamma1 -| psi
    (tau :: Gamma1)  -| os .(phi1 ++C= phi2)  | split phi1 phi2 (refl , refl)  = split (os phi1) phi2 (refl , refl)
  \end{code}
  \paragraph{Things with thinnings}
  For types indexed by a context, we have been careful to pass it as the last argument.
  This allows us talk about things in some existential scope, but with a thinning
  into a fixed one.
  \begin{code}
    record _^^_ (T : List I -> Set) (Gamma : List I) : Set where
      constructor _^_
      field
        {support} : List I
        thing : T support
        thinning : support C= Gamma
  \end{code}
  \begin{code}
    map^^   : (forall {Delta} -> S Delta -> T Delta) -> S ^^ Gamma -> T ^^ Gamma
    mult^^  : ((T ^^_) ^^_) Gamma -> T ^^ Gamma
    thin^^  : Delta C= Gamma -> T ^^ Delta -> T ^^ Gamma
  \end{code}
  % map^^ f (s ^ theta) = f s ^ theta
  % mult^^ ((t ^ theta) ^ phi) = t ^ (theta .. phi)
  % thin^^ phi (t ^ theta) = t ^ (theta .. phi)
  \paragraph{Language-related operations}
  Thinnings can be used to specify operations on the datatypes we defined for our language,
  such as environments, references and expressions.
  \Fixme{Also show laws that |_.._| commutes with operations?}
  \begin{code}
    project-Env  : Delta C= Gamma -> Env Gamma         -> Env Delta
    rename-Ref   : Delta C= Gamma -> Ref sigma Delta   -> Ref sigma Gamma
    rename-Expr  : Delta C= Gamma -> Expr sigma Delta  -> Expr sigma Gamma
  \end{code}
  Note that we can only \emph{remove} elements from environments,
  but \emph{add} further elements to the context of references and expressions.
  Furthermore, we can prove laws about how they relate to each other under evaluation,
  such as
  |eval (rename-Expr theta e) env == eval e (project-Env theta env)|
  and
  |lookup (rename-Ref theta x) env == lookup x (project-Env theta env)|.

\Fixme{Move |Expr|-independent thinning operations on |Ref|, |Env| to a separate chapter? (basically |Language.Core|)}


\section{Dead Binding Elimination}
\label{sec:de-bruijn-dbe}

\subsection{Variable Liveness}
\label{sec:de-bruijn-dbe-liveness}
    We use thinnings |Delta C= Gamma| to indicate the \emph{live variables} |Delta|
    within the context |Gamma|.
    The list |Delta| is not enough:
    If the original context contains multiple variables of the same type,
    ambiguities can arise.
    Live variables |NAT :: []| in context |NAT :: NAT :: []|
    could refer to the first or second variable in scope,
    but the thinnings |os (o' oz)| and |o' (os oz)| distinguish the two cases.
    We now need operations to merge live contexts of multiple subexpressions
    and remove bound variables.
  % Values have no live variables, |oe|
  \paragraph{Variables}
    A variable occurrence trivially has one live variable.
    To obtain a suitable thinning, We can make use of the fact that
    thinnings from a singleton context are isomorphic to references.
    \begin{code}
      o-Ref : Ref sigma Gamma -> (sigma :: []) C= Gamma
      o-Ref Top      = os oe
      o-Ref (Pop x)  = o' (o-Ref x)
    \end{code}
    % \begin{code}
    %   ref-o : (sigma :: []) C= Gamma -> Ref sigma Gamma
    %   ref-o (o' theta)  = Pop (ref-o theta)
    %   ref-o (os theta)  = Top
    % \end{code}
    % \begin{code}
    %   law-ref-o-Ref : (x : Ref sigma Gamma) -> ref-o (o-Ref x) == x
    % \end{code}
  \paragraph{Binary constructors}
    Variables from the context are live if they are live in one of the subexpressions (i.e. some thinning is |os _|).
    \begin{code}
      \/-domain : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> List I
      \/-domain                       (o' theta1)  (o' theta2)  = \/-domain theta1 theta2
      \/-domain {Gamma = sigma :: _}  (o' theta1)  (os theta2)  = sigma :: \/-domain theta1 theta2
      \/-domain {Gamma = sigma :: _}  (os theta1)  (o' theta2)  = sigma :: \/-domain theta1 theta2
      \/-domain {Gamma = sigma :: _}  (os theta1)  (os theta2)  = sigma :: \/-domain theta1 theta2
      \/-domain                       oz           oz           = []
    \end{code}
    We then construct the thinning from this combined live context.
    \Fixme{This is basically |Coproduct| as used for co-de-Bruijn. Can we avoid the duplication?}
    \begin{code}
      _\/_ : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> \/-domain theta1 theta2 C= Gamma
      o' theta1  \/ o' theta2  = o'  (theta1 \/ theta2)
      o' theta1  \/ os theta2  = os  (theta1 \/ theta2)
      os theta1  \/ o' theta2  = os  (theta1 \/ theta2)
      os theta1  \/ os theta2  = os  (theta1 \/ theta2)
      oz         \/ oz         = oz
    \end{code}
    Furthermore, we can construct the two thinnings \emph{into} the combined live context
    and show that this is exactly what we need to obtain the original thinnings.
    \begin{code}
      un-\/1 : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> Delta1 C= \/-domain theta1 theta2
      un-\/2 : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> Delta2 C= \/-domain theta1 theta2

      law-\/1-inv : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> un-\/1 theta1 theta2 .. (theta1 \/ theta2) == theta1
      law-\/2-inv : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> un-\/2 theta1 theta2 .. (theta1 \/ theta2) == theta2
    \end{code}
  \paragraph{Binders}
    The context only contains the free variables of an expression,
    so we have to pop bound variables off the context and live variables (if present).
    There are again thinnings into and out of the resulting list.
    \begin{code}
      pop-domain : Delta C= Gamma -> List I
      pop-domain {Delta = Delta}       (o' theta)  = Delta
      pop-domain {Delta = _ :: Delta}  (os theta)  = Delta
      pop-domain                       oz          = []

      pop : (theta : Delta C= (sigma :: Gamma)) -> pop-domain theta C= Gamma
      pop (o' theta)  = theta
      pop (os theta)  = theta

      un-pop : (theta : Delta C= (sigma :: Gamma)) -> Delta C= (sigma :: pop-domain theta)

      law-pop-inv : (theta : Delta C= (sigma :: Gamma)) -> un-pop theta .. os (pop theta) == theta
    \end{code}
  \paragraph{Let-bindings}
    For let-bindings, one way is to treat them as an immediate application
    of a $\lambda$-abstraction, combining the methods we just saw.
    This corresponds to a non-strong live variable analysis,
    since even if the body is dead, we end up considering the declaration
    for the live context.
    \begin{code}
      combine : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> \/-domain theta1 (pop theta2) C= Gamma
      combine theta1 theta2 = theta1 \/ pop theta2
    \end{code}
    The other option is to do strongly live variable analysis
    with a custom operation |combine|,
    which ignores the declaration's context if it is unused in the body.
    \Fixme{Is there a better name than |combine|?}
    \begin{code}
      combine-domain : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> Ctx
      combine-domain {Delta2 = Delta2}  theta1 (o' theta2)  = Delta2
      combine-domain                    theta1 (os theta2)  = \/-domain theta1 theta2

      combine : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> combine-domain theta1 theta2 C= Gamma
      combine theta1 (o' theta2)  = theta2
      combine theta1 (os theta2)  = theta1 \/ theta2
    \end{code}
    We do not need the composed thinnings into the live context,
    as we will always distinguish the two cases of |theta2| anyways.

\subsection{Direct Approach}
\label{sec:de-bruijn-dbe-direct}
    To make the decision whether a binding can be removed,
    we need to find out if it is used or not.
    We could query that information on demand
    (and we will see a similar approach in section
    \ref{sec:de-bruijn-let-sinking-direct}),
    but here we instead return liveness information as part of the result
    and use that.
    Precisely, we return |Expr sigma ^^ Gamma|,
    the transformed expression in its live context,
    together with a thinning into the original one.
  \paragraph{Transformation}
    For the thinnings we return, we make use of the variable liveness operations
    defined in the previous section.
    \begin{code}
      dbe : Expr sigma Gamma -> Expr sigma ^^ Gamma
      dbe (Var x) =
        Var Top ^ o-Ref x
      dbe (App e1 e2) =
        let  e1' ^ theta1 = dbe e1
             e2' ^ theta2 = dbe e2
        in App (rename-Expr (un-\/1 theta1 theta2) e1') (rename-Expr (un-\/2 theta1 theta2) e2')
             ^ (theta1 \/ theta2)
      dbe (Lam e1) =
        let  e1' ^ theta = dbe e1
        in Lam (rename-Expr (un-pop theta) e1') ^ pop theta
      dbe (Let e1 e2) with dbe e1 | dbe e2
      ... | e1' ^ theta1  | e2' ^ o' theta2 =
        e2' ^ theta2
      ... | e1' ^ theta1  | e2' ^ os theta2 =
        Let (rename-Expr (un-\/1 theta1 theta2) e1') (rename-Expr (os (un-\/2 theta1 theta2)) e2')
          ^ (theta1 \/ theta2)
      dbe (Val v) =
        (Val v) ^ oe
      dbe (Plus e1 e2) =
        let  e1' ^ theta1 = dbe e1
             e2' ^ theta2 = dbe e2
        in Plus (rename-Expr (un-\/1 theta1 theta2) e1') (rename-Expr (un-\/2 theta1 theta2) e2')
             ^ (theta1 \/ theta2)
    \end{code}
    For |Let|, we split on the binding being live or dead in |dbe e2|.
    Note that this only keeps the binding if it is \emph{strongly} live.
    Otherwise, we simply drop it.

    Also note that we need to rename the subexpressions at every binary operator,
    which is inefficient.
    This happens because in the |Expr| type
    both subexpressions need to have the same context,
    and cannot be avoided easily with the approach shown here.
    If we knew upfront which context the expression should have in the end,
    we could immediately produce the result in that context.
    However, we only find out which variables are live
    \emph{after} doing the recursive call.
    We will show a solution to this issue in the next section.
  \paragraph{Correctness}
    We prove preservation of semantics based on the total evaluation function.
    Since we allow functions as values, this requires us to postulate extensionality.
    This does not impact the soundness of the proof
    and could be avoided by moving to a different setting,
    such as homotopy type theory \cite{Univalent2013HomotopyTypeTheory}.
    \begin{code}
      dbe-correct :
        (e : Expr sigma Gamma) (env : Env Gamma) ->
        let e' ^ theta = dbe e
        in eval e' (project-Env theta env) == eval e env
    \end{code}
    The inductive proof requires combining a large number of laws about
    evaluation, renaming, environment projection and the thinnings we constructed.
    The |Lam| case exemplifies that.
    \Fixme{Probably more useful with |==|-Reasoning.}
    % \begin{code}
    %   dbe-correct (App e1 e2) env =
    %     let  e1' ^ theta1 = dbe e1
    %          e2' ^ theta2 = dbe e2
    %     in
    %       cong2 _S_
    %         (trans
    %           (law-eval-rename-Expr e1' _ _)
    %           (trans
    %             (cong (eval e1')
    %               (trans
    %                 (sym (law-project-Env-.. (un-\/1 theta1 theta2) (theta1 \/ theta2) env))
    %                 (cong (lambda x -> project-Env x env) (law-\/1-inv theta1 theta2))))
    %             (dbe-correct e1 env)))
    %         (trans
    %           (law-eval-rename-Expr e2' _ _)
    %           (trans
    %             (cong (eval e2')
    %               (trans
    %                 (sym (law-project-Env-.. (un-\/2 theta1 theta2) (theta1 \/ theta2) env))
    %                 (cong (lambda x -> project-Env x env) (law-\/2-inv theta1 theta2))))
    %             (dbe-correct e2 env)))
    % \end{code}
    \begin{code}
      dbe-correct (Lam e1) env =
        let e1' ^ theta1 = dbe e1
        in extensionality _ _ lambda v ->
          trans
            (law-eval-rename-Expr e1' (un-pop theta1) (project-Env (os (pop theta1)) (Cons v env)))
            (trans
              (cong (eval e1')
                (trans
                  (sym (law-project-Env-.. (un-pop theta1) (os (pop theta1)) (Cons v env)))
                  (cong (lambda x -> project-Env x (Cons v env)) (law-pop-inv theta1))))
              (dbe-correct e1 (Cons v env)))
      (dots)
    \end{code}

\subsection{Using Live Variable Analysis}
\label{sec:de-bruijn-dbe-live}
    In compilers, it is a common pattern to perform
    separate analysis and transformation passes,
    for example with strictness and occurrence analysis in GHC
    \cite{Jones1998TransformationOptimiser}.
    We can do the same to make variable liveness information available
    without repeatedly having to computing it on the fly.
    For dead binding elimination,
    this allows us to avoid the redundant renaming of subexpressions.
  \paragraph{Liveness annotations}
    To annotate each part of the expression with its live context,
    we first need to define a suitable datatype of annotated expressions
    |LiveExpr tau theta|.
    The thinning |theta| here will be the same as we returned from the
    transformation in section \ref{sec:de-bruijn-dbe-direct}.
    \begin{code}
      data LiveExpr {Gamma : Ctx} : U -> {Delta : Ctx} -> Delta C= Gamma -> Set where
        Var :
          (x : Ref sigma Gamma) ->
          LiveExpr sigma (o-Ref x)
        App :
          {theta1 : Delta1 C= Gamma} {theta2 : Delta2 C= Gamma} ->
          LiveExpr (sigma => tau) theta1 ->
          LiveExpr sigma theta2 ->
          LiveExpr tau (theta1 \/ theta2)
        Lam :
          {theta : Delta C= (sigma :: Gamma)} ->
          LiveExpr tau theta ->
          LiveExpr (sigma => tau) (pop theta)
        Let :
          {theta1 : Delta1 C= Gamma} {theta2 : Delta2 C= (sigma :: Gamma)} ->
          LiveExpr sigma theta1 ->
          LiveExpr tau theta2 ->
          LiveExpr tau (combine theta1 theta2)
        Val :
          (interpretU(sigma)) ->
          LiveExpr sigma oe
        Plus :
          {theta1 : Delta1 C= Gamma} {theta2 : Delta2 C= Gamma} ->
          LiveExpr NAT theta1 ->
          LiveExpr NAT theta2 ->
          LiveExpr NAT (theta1 \/ theta2)
    \end{code}
  \paragraph{Analysis}
    To create such an annotated expressions, we need to perform
    strongly live variable analysis.
    The function |analyse| computes an existentially qualified live context and thinning,
    together with a matching annotated expression.
    \begin{code}
      analyse : Expr sigma Gamma -> (Exists (Delta) Ctx) (Exists (theta) (Delta C= Gamma)) LiveExpr sigma theta
      analyse (Var {sigma} x) = sigma :: [] , o-Ref x , Var x
      analyse (App e1 e2) =
        let  Delta1 , theta1 , le1 = analyse e1
             Delta2 , theta2 , le2 = analyse e2
        in \/-domain theta1 theta2 , (theta1 \/ theta2) , App le1 le2
      (dots)
    \end{code}
    It is sensible to assume that the only thing analysis does
    is to attaches annotations without changing the structure of the expression.
    We capture this property by stating that we can always forget the annotations
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
      (dots)
      evalLive (Let {theta1 = theta1} {theta2 = o' theta2} e1 e2) env theta' =
        evalLive e2 env theta'
      evalLive (Let {theta1 = theta1} {theta2 = os theta2} e1 e2) env theta' =
        evalLive e2
          (Cons (evalLive e1 env (un-\/1 theta1 theta2 .. theta')) env)
          (os (un-\/2 theta1 theta2 .. theta'))
      (dots)
    \end{code}
    We will later use this to split the correctness proof into multiple small parts.
  \paragraph{Transformation}
    The second pass we perform is similar to |dbe| in the direct approach,
    but with a few key differences.
    Firstly, it operates on annotated expressions |LiveExpr tau theta|
    for a known thinning |theta : Delta C= Gamma| instead of discovering the
    thinning and returning it with the result.
    However, the transformed expression will not just be indexed by
    the live context |Delta|, but any chosen larger context |Gamma'|.
    Instead of renaming afterwards,
    the result gets created in the desired context straight away.
    Most cases now simply recurse while accumulating the thinning
    that eventually gets used to create the variable reference.
    \begin{code}
      transform : {theta : Delta C= Gamma} -> LiveExpr tau theta -> Delta C= Gamma' -> Expr tau Gamma'
      transform (Var x) theta' =
        Var (ref-o theta')
      transform (App {theta1 = theta1} {theta2 = theta2} e1 e2) theta' =
        App  (transform e1 (un-\/1 theta1 theta2 .. theta'))
             (transform e2 (un-\/2 theta1 theta2 .. theta'))
      transform (Lam {theta = theta} e1) theta' =
        Lam (transform e1 (un-pop theta .. os theta'))
      transform (Let {theta1 = theta1} {theta2 = o' theta2} e1 e2) theta' =
        transform e2 theta'
      transform (Let {theta1 = theta1} {theta2 = os theta2} e1 e2) theta' =
        Let  (transform e1 (un-\/1 theta1 theta2 .. theta'))
             (transform e2 (os (un-\/2 theta1 theta2 .. theta')))
      transform (Val v) theta' =
        Val v
      transform (Plus {theta1 = theta1} {theta2 = theta2} e1 e2) theta' =
        Plus  (transform e1 (un-\/1 theta1 theta2 .. theta'))
              (transform e2 (un-\/2 theta1 theta2 .. theta'))
    \end{code}
    We can now compose analysis and transformation into an operation
    with the same signature as the direct implementation
    in section \ref{sec:de-bruijn-dbe-direct}.

  \begin{code}
    dbe : Expr sigma Gamma -> Expr sigma ^^ Gamma
    dbe e = let _ , theta , le = analyse e in transform le oi ^ theta
  \end{code}

  \paragraph{Correctness}
    The goal is again to show that dead binding elimination preserves semantics,
    which we can express with the same statement as before,
    or conceptually as |eval . dbe == eval|.
    \begin{code}
      dbe-correct :
        (e : Expr sigma Gamma) (env : Env Gamma) ->
        let e' ^ theta = dbe e
        in eval e' (project-Env theta env) == eval e env
    \end{code}
    % |eval . transform . analyse == eval|.
    We could again immediately attempt a proof by structural induction,
    but each case would require cumbersome massaging
    of the thinnings supplied to various operations.
    Instead, we aim to simplify the proof by breaking it down into
    smaller parts.
    The first observation is that it is sufficient to show the following:
    \begin{code}
      eval . transform == eval . forget
    \end{code}
    We can then pre-compose |analyse| on both sides and remove
    |forget . analyse| (which we know forms an identity)
    to obtain the desired |eval . transform . analyse == eval|.
    The proof gets simpler if we split it up using the optimised semantics:
    \begin{code}
      evalLive == eval . forget
      evalLive == eval . transform
    \end{code}
    \Outline{
      The actual proof statements in Agda are more involved,
      since they quantify over the expression and environment used for evaluation.
      As foreshadowed in the definition of |evalLive|,
      the statements are also generalised to evaluation under any |Env Gamma'|,
      as long as it contains the live context.
      This gives us more flexibility when using the inductive hypothesis.

      Both proofs work inductively on the expression, with most cases being a straight-forward congruence.
      The interesting one is again |Let|, where we split cases on the variable being used or not
      and need some auxiliary facts about evaluation, renaming and contexts.
    }
    \Fixme{show exact proof statements}
    \OpenEnd{Some details to be figured out to make sure the modular proof is indeed simpler.}


\section{Let-sinking}
\label{sec:de-bruijn-let-sinking}

\subsection{Direct Approach}
\label{sec:de-bruijn-let-sinking-direct}
    We want to push a let-binding as far inward as possible,
    without pushing into a $\lambda$-abstraction or duplicating the binding.
  \paragraph{Type signature}
    While we initially deal with a binding for the topmost entry in the context
    (|Expr sigma Gamma -> Expr tau (sigma :: Gamma) -> Expr tau Gamma|),
    recursively applying this function under binders requires more flexibility.
    The solution chosen here uses list concatenation in the context
    to allow |sigma| to occur at any position.
    Choosing |[]| as the prefix then again results in the same signature
    as the for the |Let| constructor itself.
    \begin{code}
      sink-let : Expr sigma (Gamma1 ++ Gamma2)  -> Expr tau (Gamma1 ++ sigma :: Gamma2)  -> Expr tau (Gamma1 ++ Gamma2)
    \end{code}
    Note that we could alternatively have used other ways to achieve the same,
    such as insertion at a position |n : Fin (length Gamma)|
    or removal of |sigma| at a position |i : Ref sigma Gamma|.
      \Fixme{Does this belong to a later alternative design section?}
    \begin{code}
      pop-at : (Gamma : Ctx) -> Ref sigma Gamma -> Ctx
      pop-at (sigma :: Gamma) Top = Gamma
      pop-at (tau   :: Gamma) (Pop i) = tau :: pop-at Gamma i
    \end{code}
    \begin{code}
      Expr sigma (Gamma1 ++ Gamma2)  -> Expr tau (Gamma1 ++ sigma :: Gamma2)  -> Expr tau (Gamma1 ++ Gamma2)
      Expr sigma (pop-at Gamma i)    -> Expr tau Gamma                        -> Expr tau (pop-at Gamma i)
      Expr sigma Gamma               -> Expr tau (insert n sigma Gamma)       -> Expr tau Gamma
    \end{code}
    Using list concatenation, however, allows us to make use of very general
    operations and properties about concatenation of contexts and thinnings.
  \paragraph{Transformation}
    The implementation proceeds by structural induction.
    \begin{code}
      sink-let : Expr sigma (Gamma1 ++ Gamma2) -> Expr tau (Gamma1 ++ sigma :: Gamma2) -> Expr tau (Gamma1 ++ Gamma2)
      sink-let decl (Var x) with rename-top-Ref x
      ... | Top = decl
      ... | Pop x' = Var x'
      sink-let decl (At(e)(App e1 e2)) with strengthen e1 | strengthen e2
      ... | just e1'  | just e2'  = App e1' e2'
      ... | nothing   | just e2'  = App (sink-let decl e1) e2'
      ... | just e1'  | nothing   = App e1' (sink-let decl e2)
      ... | nothing   | nothing   = Let decl (rename-top e)
      sink-let decl (At(e)(Lam e1)) =
        Let decl (rename-top e) -- Do not push into $\lambda$-abstractions!
      sink-let {Gamma1 = Gamma1} decl (At(e)(Let e1 e2)) with strengthen e1 | strengthen {Gamma1 = _ :: Gamma1} e2
      ... | just e1'  | just e2'  = Let e1' e2'
      ... | nothing   | just e2'  = Let (sink-let decl e1) e2'
      ... | just e1'  | nothing   = Let e1' (sink-let {Gamma1 = _ :: Gamma1} (weaken decl) e2)
      ... | nothing   | nothing   = Let decl (rename-top e)
      sink-let decl (Val v) =
        Val v
      sink-let decl (At(e)(Plus e1 e2)) with strengthen e1 | strengthen e2
      ... | just e1'  | just e2'  = Plus e1' e2'
      ... | nothing   | just e2'  = Plus (sink-let decl e1) e2'
      ... | just e1'  | nothing   = Plus e1' (sink-let decl e2)
      ... | nothing   | nothing   = Let decl (rename-top e)
    \end{code}
    We will highlight specific parts.
    \Fixme{Split up cases or leave as one block?}
  \paragraph{Variables}
    When pushing a binding into a variable, there are two possible cases:
    \begin{enumerate}
      \item If the variable references exactly the let-binding we are sinking,
        we can replace it by the declaration,
        effectively inlining it.
      \item If the variable references a different element of the context,
        the declaration is unused
        and we  only need to strengthen the variable into the smaller context.
    \end{enumerate}
    To distinguish the two cases, we rename the reference
    (moving the variable in question to the front).
    \begin{code}
      rename-top-Ref : Ref tau (Gamma1 ++ sigma :: Gamma2) -> Ref tau (sigma :: Gamma1 ++ Gamma1)
    \end{code}
    If the result is |Top|, we learn that |sigma == tau| and can return the declaration.
    If it is |Pop x'|, we can return |x'|,
    as it does not have the variable of the declaration in its context anymore.
  \paragraph{Creating the binding}
    Once we stop pushing the let-binding (e.g. when we reach a $\lambda$-abstraction),
    We insert the declaration.
    However, the typechecker will not accept |Let decl e|.
    It is still necessary to rename the expression,
    since it makes use of the newly created binding,
    but expects it at a different de Bruijn index.
    \begin{code}
      rename-top : Expr tau (Gamma1 ++ sigma :: Gamma2) -> Expr tau (sigma :: Gamma1 ++ Gamma2)
    \end{code}
  \paragraph{Binary constructors}
    For binary operators, we need to check which subexpressions make use of the declaration.
    Instead of working with an annotated version of the syntax tree,
    we here query variable usage in subexpressions on demand.
    Since usage information is computed bottom-up,
    but let-sinking works top-down,
    we redundantly traverse the whole expression at each binary constructor
    of the expression.
    Perhaps unsurprisingly, we will see that we can again change that
    using liveness annotations.

    If the binding is not used in a subexpression,
    we need to obtain a strengthened version of that expression,
    so we make it part of the querying operation.
    \begin{code}
      strengthen :  Expr tau (Gamma1 ++ sigma :: Gamma2) -> Maybe (Expr tau (Gamma1 ++ Gamma2))
    \end{code}
    We now see that there are four possible cases:
    \begin{enumerate}
      \item
        Both of the subexpressions can be strengthened.
        This means that we are sinking a dead let-binding,
        which normally should not happen.
        Nevertheless, we need to handle the case.
      \item
        The right subexpression can be strengthened.
        We recurse into the left one.
      \item
        The left subexpression can be strengthened.
        We recurse into the right one.
      \item
        Neither subexpression can be strengthened, as both use the declaration.
        To avoid dupliating code, we do not push further,
        but create a let-binding at the current location.
    \end{enumerate}
  \paragraph{Binders}
    If we recurse into the body of a let-binding,
    an additional variable comes into scope.
    This means that we need to add it to the context prefix |Gamma1|
    and weaken the declaration.
    \begin{code}
      weaken : Expr tau Gamma -> Expr tau (sigma :: Gamma)
    \end{code}
  \paragraph{Correctness}
    \OpenEnd{No correctness proof yet, how hard is it for the direct approach?}

\subsection{Using Live Variable Analysis}
\label{sec:de-bruijn-let-sinking-live}
  \Outline{
    We can solve repeated-querying-problem with liveness annotations again.
    First |analyse| and then (instead of strengthening), just look at thinning.
    (how?)
  }
  \paragraph{Type signature}
    Similarly to section \ref{sec:de-bruijn-dbe-live},
    we first perform the analysis and then a transformation,
    resulting in a plain |Expr| again.
    Combined, this has the same signature as the direct version.
    \begin{code}
      transform :
        {theta : Delta C= (Gamma1 ++ sigma :: Gamma2)} ->
        Expr sigma (Gamma1 ++ Gamma2) ->
        LiveExpr tau theta ->
        Expr tau (Gamma1 ++ Gamma2)
    \end{code}
    \begin{code}
      sink-let : Expr sigma (Gamma1 ++ Gamma2) -> Expr tau (Gamma1 ++ sigma :: Gamma2)  -> Expr tau (Gamma1 ++ Gamma2)
      sink-let decl e = let _ , theta , le = analyse e in transform decl le
    \end{code}
  \paragraph{Creating the binding}
    This is almost identical to before,
    but we now need to |forget| the annotations before calling |rename-top|.
  \paragraph{Binary constructors}
    We call |_-||_| on the thinnings of the subexpressions
    to find out where the declaration is used.
    For the subexpressions where the variable |sigma| bound to the declaration
    does not occur, the |Split| exposes that their thinning |theta|
    into |Gamma1 ++ sigma :: Gamma2| is of the form |theta1 ++C= o' theta2|,
    so we can construct a new thinning |theta1 ++C= theta2|
    into |Gamma1 ++ Gamma2|.
    \Fixme{More consistent naming of thinnings involved}
    To obtain the required un-annotated expression
    (that does not have the declaration in its context anymore),
    we can then use |DBE.transform|.
  \paragraph{Binders}
    We still weaken the declaration every time we go under a binder.
    This is somewhat inefficient,
    as weakening an expression in de Bruijn representation requires a traversal,
    but could easily be avoided by instead passing a declaration with a thinning
    |Expr tau ^^ Gamma| and composing the thinning.
    We would then only need to rename the declaration once at the end,
    when the binding is created.


\section{Discussion}
\label{sec:de-bruijn-discussion}
    \Outline{
      We implemented two transformation,
      each first directly (exhibiting inherent flaws)
      and then using liveness annotations.
      While this requires a separate analysis pass
      and requires additional code,
      it solved the issues with the direct approach
      and simplified some aspects.
    }
    \Outline{Generally, what caused issues, what was nice?}
    \Outline{re-ordering context does not fit thinnings nicely.}
    \Outline{Let-sinking also performs DBE, but only for a single binding.}

\subsection{Alternative Designs}
  \paragraph{More flexible annotations}
    \Outline{|LiveExpr| not required to be tight.}
  \paragraph{Iterating transformations}
    \Outline{e.g. without strong, but also for more complicated analyses}
    \Draft{
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
    }
  \paragraph{Keeping annotations}
    \Outline{
      Transformations could also return annotated expression
      (why throw away information?).
      But more complex, annotations need to be reconstructed on the way up.
      Maybe this could be factored out?
      However, also other practical issues.
    }
    \Outline{
      Note that it might generally be useful to stay in |LiveExpr| world all the time.
      Usage information is nice, but complicated to maintain.
      Doing it for let-sinking caused issues.
      There remains redundancy around indexing by two scopes.
      Could co-de-Bruijn give us the same benefits by default?
      It would also help with CSE (equality of terms).
    }

  \vspace{0.5cm}
  \OpenEnd{Let-sinking multiple bindings at once?}
