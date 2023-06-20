%include agda.fmt
%include custom.fmt

\chapter{De Bruijn Representation}
\label{ch:de-bruijn}
    The main objective of this chapter is to show
    how to manipulate the binding structure of intrinsically typed de Bruijn syntax.
    We start by demonstrating how the intrinsically typed representation
    enforces type- and scope-correctness by making the context of expressions explicit
    in their type.
    To talk about the relationship between contexts,
    we give an introduction to thinnings and some operations on them that will prove useful later.
    This leads us to the discovery that thinnings can nicely capture the notion of variable liveness,
    which is fundamental for manipulating bindings.
    Finally, we use them to describe program transformations and prove their correctness.

    For brevity, we will make use of Agda's ability to quantify over variables implicitly.
    The types of these variables should be clear from their names and context.

\section{Intrinsically Typed Syntax}
\label{sec:de-bruijn-intrinsically-typed}
    Whether we use explicit names or de Bruijn indices,
    the language as seen so far makes it possible to represent expressions
    that are ill-typed (e.g. performing addition on Booleans)
    or -scoped.
    In Agda, we can similarly define expressions as follows:
    \begin{code}
      data RawExpr : Set where
        Var   : Nat -> RawExpr
        App   : RawExpr -> RawExpr -> RawExpr
        Lam   : RawExpr -> RawExpr
        Let   : RawExpr -> RawExpr -> RawExpr
        Num   : Nat -> RawExpr
        Bln   : Bool -> RawExpr
        Plus  : RawExpr -> RawExpr -> RawExpr
    \end{code}

    But how should expressions like |Plus (Bln False) (Var 42)| be evaluated?
    What is the result of adding Booleans and how do we ensure that a value
    (of the right type) is provided for each variable used?
    Clearly, evaluating such an expression must lead to a runtime error.

  \paragraph{Sorts}
    The first problem can be addressed by indexing each expression
    with its \emph{sort} |U|, the type that it should be evaluated to.
    \begin{code}
      data U : Set where
        _=>_  : U -> U -> U
        BOOL  : U
        NAT   : U

      variable
        sigma tau : U

      interpretU_ : U -> Set
      (interpretU(sigma => tau))  = (interpretU(sigma)) -> (interpretU(tau))
      (interpretU(BOOL))          = Bool
      (interpretU(NAT))           = Nat

      data RawExpr : U -> Set where
        Var   : Nat -> RawExpr sigma
        App   : RawExpr (sigma => tau) -> RawExpr sigma -> RawExpr tau
        Lam   : RawExpr tau -> RawExpr (sigma => tau)
        Let   : RawExpr sigma -> RawExpr tau -> RawExpr tau
        Val   : (interpretU(sigma)) -> RawExpr sigma
        Plus  : RawExpr NAT -> RawExpr NAT -> RawExpr NAT
    \end{code}

    Note that the values not only consist of natural numbers and Booleans,
    but also functions between values,
    introduced by $\lambda$-abstraction.
    Sorts can further be interpreted as Agda types,
    which we use to represent values, for example during evaluation.

  \paragraph{Context}
    Sorts help, but to know if a variable occurrence is valid,
    one must also consider its \emph{context},
    the (typed) bindings that are in scope.
    We represent the context as a list of sorts:
    One for each binding in scope, from innermost to outermost.
    \begin{code}
      Ctx = List U

      variable
        Gamma Delta : Ctx
    \end{code}
    De Bruijn indeces can then ensure that they reference an element of a specific type within the context.
    \begin{code}
      data Ref (sigma : U) : Ctx -> Set where
        Top  : Ref sigma (sigma :: Gamma)
        Pop  : Ref sigma Gamma -> Ref sigma (tau :: Gamma)
    \end{code}

    By also indexing expressions with their context,
    the invariants can finally guarantee type- and scope-correctness by construction.
    \begin{code}
      data Expr : (Gamma : Ctx) (tau : U) -> Set where
        Var   : Ref sigma Gamma -> Expr sigma Gamma
        App   : Expr (sigma => tau) Gamma -> Expr sigma Gamma -> Expr tau Gamma
        Lam   : Expr tau (sigma :: Gamma) -> Expr (sigma => tau) Gamma
        Let   : Expr sigma Gamma -> Expr tau (sigma :: Gamma) -> Expr tau Gamma
        Val   : (interpretU(sigma)) -> Expr sigma Gamma
        Plus  : Expr NAT Gamma -> Expr NAT Gamma -> Expr NAT Gamma
    \end{code}
    Note how the context changes when introducing a new binding
    in the body of a |Lam| or |Let|.

  \paragraph{Evaluation}
    During evaluation, each variable in scope has a value.
    Together, these are called an \emph{environment} for a given context.
    \begin{code}
      data Env : Ctx -> Set where
        Nil   : Env []
        Cons  : (interpretU(sigma)) -> Env Gamma -> Env (sigma :: Gamma)
    \end{code}

    Since variable |Ref sigma Gamma| acts as a proof that
    the environment |Env Gamma| contains an element of type |sigma|,
    variable lookup is total.
    \begin{code}
      lookup : Ref sigma Gamma -> Env Gamma -> (interpretU(sigma))
      lookup Top      (Cons v env)   = v
      lookup (Pop i)  (Cons v env)   = lookup i env
    \end{code}

    As a result, we can define a total evaluator
    that can only be called with an environment that matches the expression's context.
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
\label{sec:de-bruijn-thinnings}
    Since the context of an expression plays such an important role for its scope-safety,
    we want some machinery for talking about how different contexts relate to each other.
    One such relation, which will prove useful soon,
    is that of being a subcontext,
    or more precisely a context with an embedding into another.
    We formalise this notion in the form of \emph{thinnings},
    also called \emph{order-preserving embeddings} (OPE)
    \cite{Chapman2009TypeCheckingNormalisation}.

    As several operations on thinnings are used pervasively
    throughout the rest of the thesis,
    we briefly introduce them here in a central location we can refer back to.
    Their applications will become apparent starting from section
    \ref{sec:de-bruijn-dbe}.

    We closely follow the syntactic conventions of McBride
    \cite{McBride2018EveryBodysGotToBeSomewhere},
    but grow our lists towards the left
    instead of using backwards lists and postfix operators.
    \begin{code}
      data _C=_ {I : Set} : List I -> List I -> Set where
        o' : Delta C= Gamma ->          Delta   C= (tau :: Gamma)    -- drop
        os : Delta C= Gamma -> (tau ::  Delta)  C= (tau :: Gamma)    -- keep
        oz : [] C= []                                                -- empty
    \end{code}

    Intuitively, a thinning tells us for each element of the target context
    whether it also occurs in the source target or not (\emph{keep} or \emph{drop}).
    As an example, let us embed the list |a :: c :: []| into |a :: b :: c :: []|:
    \begin{code}
      os (o' (os oz)) : (a :: c :: []) C= (a :: b :: c :: [])
    \end{code}

  \paragraph{Identity and composition}
    Contexts and the thinnings between them form a category
    with the inital object |[]|.
    Concretely, this means that there is an empty and identity thinning
    (keeping none or all elements, respectively),
    as well as composition of thinnings in sequence,
    followingidentity and associativity laws.
    \begin{code}
      oe : [] C= Gamma
      oe {Gamma = []}      = oz
      oe {Gamma = _ :: _}  = o' oe

      oi : Gamma C= Gamma
      oi {Gamma = []}      = oz
      oi {Gamma = _ :: _}  = os oi

      _.._ : Gamma1 C= Gamma2 -> Gamma2 C= Gamma3 -> Gamma1 C= Gamma3
      theta     .. o' phi  = o' (theta .. phi)
      o' theta  .. os phi  = o' (theta .. phi)
      os theta  .. os phi  = os (theta .. phi)
      oz        .. oz      = oz

      law-..oi  :  (theta : Delta C= Gamma) -> theta .. oi == theta
      law-oi..  :  (theta : Delta C= Gamma) -> oi .. theta == theta
      law-....  :  (theta : Gamma1 C= Gamma2) (phi : Gamma2 C= Gamma3) (psi : Gamma3 C= Gamma4) ->
                   theta .. (phi .. psi) == (theta .. phi) .. psi
    \end{code}

  \paragraph{Concatenating thinnings}
    Thinnings cannot just be composed in sequence, but also concatenated.
    \begin{code}
      _++C=_ : Delta1 C= Gamma1 -> Delta2 C= Gamma2 -> (Delta1 ++ Delta2) C= (Gamma1 ++ Gamma2)
      o' theta  ++C= phi = o'  (theta ++C= phi)
      os theta  ++C= phi = os  (theta ++C= phi)
      oz        ++C= phi = phi
    \end{code}
    This interacts nicely with sequential composition, specifically we prove that
    |(theta1 .. theta2) ++C= (phi1 .. phi2) == (theta1 ++C= phi1) .. (theta2 ++C= phi2)|.

  \paragraph{Splitting thinnings}
    If we have a thinning into a target context that is concatenated from two segments,
    we can also split the source context and thinning accordingly.
    To help the typechecker figure out what we want, we quantify over |Gamma1| explicitly,
    |Gamma2| can then usually be inferred.
    \begin{code}
      record Split (Gamma1 : List I) (theta : Delta C= (Gamma1 ++ Gamma2)) : Set where
        constructor split
        field
          {Delta1} : List I
          {Delta2} : List I
          theta1 : (Delta1 C= Gamma1)
          theta2 : (Delta2 C= Gamma2)
          eq : Sigma (Delta == Delta1 ++ Delta2) lambda { refl -> theta == theta1 ++C= theta2 }
    \end{code}
    \begin{code}
      _-|_ : (Gamma1 : List I) (theta : Delta C= (Gamma1 ++ Gamma2)) -> Split Gamma1 theta
    \end{code}

    To show it in action, let us return to the previous example thinning
    and observe that we could have built it by concatenating two smaller thinnings:
    \begin{code}
      theta1 : (a :: []) C= (a :: [])
      theta1 = os oz

      theta2 : (c :: []) C= (b :: c :: [])
      theta2 = o' (os oz)

      theta : (a :: c :: []) C= (a :: b :: c :: [])
      theta = theta1 ++C= theta2    -- evaluates to |os (o' (os oz))|
    \end{code}
    To go into the other direction, we split |theta| by calling |(a :: []) -|| theta|,
    resulting in a |split theta1 theta2 eq : Split (a :: []) theta|.
    The target context's first segment (a :: []) needs to be supplied explicitly
    to specify at which place the splitting should happen.
    The second segment is then determined by |theta|'s target context.

  \paragraph{Things with thinnings}
    We will later deal with things (e.g. expressions) indexed by a context
    that we do not statically know.
    We will know, however, that it embeds into a specific context |Gamma| via some thinning.
    As we have so far been careful to always use the context as the last argument to types,
    this concept of a thing with a thinning can be defined in a general way,
    to be used for a wide range of different datatypes.
    \begin{code}
      record _^^_ (T : List I -> Set) (Gamma : List I) : Set where
        constructor _^_
        field
          {Delta} : List I
          thing : T Delta
          thinning : Delta C= Gamma
    \end{code}

    To avoid manual un- and re-packing, some combinators come in handy:
    \begin{code}
      map^^   : (forall {Delta} -> S Delta -> T Delta)     -> S  ^^ Gamma  -> T ^^ Gamma
      bind^^  : (forall {Delta} -> S Delta -> T ^^ Delta)  -> S  ^^ Gamma  -> T ^^ Gamma
      thin^^  : Delta C= Gamma                             -> T  ^^ Delta  -> T ^^ Gamma
    \end{code}


\section{Variable Liveness}
\label{sec:de-bruijn-liveness}
    We want to compute an expression's \emph{live variables},
    i.e. the part of the context that is live.
    However, while an expression's context is just a list of sorts,
    a similar list is not sufficient as the result of this bottom-up analysis.

    For example, knowing that two subexpressions both have a single
    live variable of sort |NAT| is not enough to deduce whether the
    combined expression has one or two live variables.
    We cannot know whether the two variables are the same,
    unless we have a way to connect them back to the context they come from.
    Another way of thinking about variable liveness is that
    for each variable in the context we want a binary piece of information:
    is it live or dead?

    Thinnings support both of these interpretations:
    A thinning |Delta C= Gamma| can be used to represent the live variables |Delta|
    together with an embedding into the context |Gamma|.
    At the same time, looking at how it is constructed
    reveals for each element of the context whether it is live (|os|) or dead (|o'|).

    We will now show for each constructor of our language
    how to compute its live variables,
    or rather their thinning into the context.

  \paragraph{Values}
    Starting with the most trivial case, values do not use any variables.
    The thinning from the (empty) list of their life variables consequently drops everything.
    \begin{code}
      oe : [] C= Gamma
    \end{code}

  \paragraph{Variables}
    A variable occurrence trivially has one live variable.
    To obtain a suitable thinning, we can make use of the fact that
    thinnings from a singleton context are isomorphic to references.
    \begin{code}
      o-Ref : Ref sigma Gamma -> (sigma :: []) C= Gamma
      o-Ref Top      = os oe
      o-Ref (Pop x)  = o' (o-Ref x)
    \end{code}
    \begin{code}
      Ref-o : (sigma :: []) C= Gamma -> Ref sigma Gamma
      Ref-o (o' theta)  = Pop (Ref-o theta)
      Ref-o (os theta)  = Top
    \end{code}

  \paragraph{Binary constructors}
    Variables in the context are live if they are live in one of the subexpressions (i.e. some thinning is |os _|).
    \begin{code}
      \/-vars : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> List I
      \/-vars                       (o' theta1)  (o' theta2)  =           \/-vars theta1 theta2
      \/-vars {Gamma = sigma :: _}  (o' theta1)  (os theta2)  = sigma ::  \/-vars theta1 theta2
      \/-vars {Gamma = sigma :: _}  (os theta1)  (o' theta2)  = sigma ::  \/-vars theta1 theta2
      \/-vars {Gamma = sigma :: _}  (os theta1)  (os theta2)  = sigma ::  \/-vars theta1 theta2
      \/-vars                       oz           oz           = []
    \end{code}
    To precisely describe the merged variable liveness information,
    we then construct a thinning from these combined live variables.
    \begin{code}
      _\/_ : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> \/-vars theta1 theta2 C= Gamma
      o' theta1  \/ o' theta2  = o'  (theta1 \/ theta2)
      o' theta1  \/ os theta2  = os  (theta1 \/ theta2)
      os theta1  \/ o' theta2  = os  (theta1 \/ theta2)
      os theta1  \/ os theta2  = os  (theta1 \/ theta2)
      oz         \/ oz         = oz
    \end{code}
    Furthermore, we can construct the two thinnings \emph{into} the combined live variables
    and show that this is exactly what we need to reconstruct the original thinnings.
    \begin{code}
      un-\/1 : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> Delta1 C= \/-vars theta1 theta2
      un-\/2 : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> Delta2 C= \/-vars theta1 theta2
    \end{code}
    \begin{code}
      law-\/1-inv :  (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) ->
                     un-\/1 theta1 theta2 .. (theta1 \/ theta2) == theta1
      law-\/2-inv :  (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) ->
                     un-\/2 theta1 theta2 .. (theta1 \/ theta2) == theta2
    \end{code}

  \paragraph{Binders}
    When moving up over a binder, the bound variable gets removed from the context.
    In case it was part of the live variables, it also has to be removed there.
    This is done using |pop|,
    again with thinnings from and into the resulting context.
    \begin{code}
      pop-vars : Delta C= Gamma -> List I
      pop-vars {Delta = Delta}       (o' theta)  = Delta
      pop-vars {Delta = _ :: Delta}  (os theta)  = Delta
      pop-vars                       oz          = []

      pop : (theta : Delta C= (sigma :: Gamma)) -> pop-vars theta C= Gamma
      pop (o' theta)  = theta
      pop (os theta)  = theta
    \end{code}
    \begin{code}
      un-pop : (theta : Delta C= (sigma :: Gamma)) -> Delta C= (sigma :: pop-vars theta)

      law-pop-inv : (theta : Delta C= (sigma :: Gamma)) -> un-pop theta .. os (pop theta) == theta
    \end{code}

  \paragraph{Let-bindings}
    For let-bindings, one option is to treat them as an immediate application
    of a $\lambda$-abstraction, combining the methods we just saw.
    This corresponds to weakly live variable analysis,
    since even if the variable is dead, we end up considering other variables to be live
    if they are used in its declaration.
    \begin{code}
      _\l/_ : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> \/-vars theta1 (pop theta2) C= Gamma
      theta1 \l/ theta2 = theta1 \/ pop theta2
    \end{code}
    The other option is to do strongly live variable analysis
    with a custom operation |_\l/_|
    that ignores the declaration's context if it is unused in the body.
    \begin{code}
      \l/-vars : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> Ctx
      \l/-vars {Delta2 = Delta2}  theta1 (o' theta2)  = Delta2
      \l/-vars                    theta1 (os theta2)  = \/-vars theta1 theta2

      _\l/_ : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> \l/-vars theta1 theta2 C= Gamma
      theta1 \l/ (o' theta2)  = theta2
      theta1 \l/ (os theta2)  = theta1 \/ theta2
    \end{code}
    We do not need the composed thinnings into the live variables,
    as we will always distinguish the two cases of |theta2| anyways
    and can then rely on the thinnings defined for |_\/_|.

    To illustrate the difference, let us return to an example shown earlier:
    \begin{align*}
      &\Let{x} 42 \In            & &\LetB 42 \In                       \\
      &\ \ \Let{y} x + 6 \In     & &\ \ \LetB \DeBruijn{0} + 6 \In     \\
      &\ \ \ \ \Let{z} y + 7 \In & &\ \ \ \ \LetB \DeBruijn{0} + 7 \In \\
      &\ \ \ \ \ \ x             & &\ \ \ \ \ \ \DeBruijn{2}
    \end{align*}
    If we focus on the subexpression in the last two lines,
    we see that in our syntax representation it is an |Expr NAT (NAT :: NAT :: [])|,
    where the first element of the context correspondes to $y$,
    the second to $x$.
    \begin{code}
      Let (Plus (Var Top) (Val 7))
        (Var (Pop (Pop Top)))
    \end{code}
    In the declaration, only the innermost binding $y$ is live,
    so we have a thinning |os (o' oz)|.
    In the body (with an additional binding in scope),
    we have |o' (o' (os oz))|.
    With the weak version of |_\l/_| we get
    \begin{code}
      os (o' oz) \l/ o' (o' (os oz)) = os (o' oz) \/ o' (os oz) = os (os oz)
    \end{code}
    stating that both variables in scope are live.
    With the strong version, on the other hand,
    only $y$ is considered live:
    \begin{code}
      os (o' oz) \l/ o' (o' (os oz)) = os (o' oz)
    \end{code}


\section{Dead Binding Elimination}
\label{sec:de-bruijn-dbe}

\subsection{Direct Approach}
\label{sec:de-bruijn-dbe-direct}
    To make the decision whether a binding can be removed,
    we need to find out if it is used or not.
    This can be achieved by returning liveness information
    as part of the transformation's result and use that after the recursive call on the body.
    Precisely, we return an |Expr sigma ^^ Gamma|,
    the transformed expression in a reduced context of only its live variables,
    together with a thinning into the original one.

  \paragraph{Transformation}
    The transformation proceeds bottom-up.
    Once all subexpressions have been transformed and we know their live variables,
    we calculate the overall live variables with their corresponding thinnings.
    Since the constructors of |Expr| require the subexpressions' context to match their own,
    we need to rename the subexpressions accordingly.
    \begin{code}
      rename-Ref   : Delta C= Gamma -> Ref sigma Delta   -> Ref sigma Gamma
      rename-Expr  : Delta C= Gamma -> Expr sigma Delta  -> Expr sigma Gamma
    \end{code}

    Each renaming traverses the expression
    and we end up renaming the same parts of the expressions repeatedly
    (at each binary constructor).
    While this is clearly inefficient,
    it cannot be avoided easily with the approach shown here.
    If we knew upfront which context the expression should have in the end,
    we could immediately produce the result in that context,
    but we only find out which variables are live
    \emph{after} doing the recursive call.
    Separately querying liveness before doing the recursive calls
    would also require redundant traversals,
    but we will show a solution to this issue in the next section.

    Most cases of the implementation keep the expression's structure unchanged,
    only manipulating the context:
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
        (dots)  -- just as App
    \end{code}
    For |Let|, we split on the binding being live or dead in |dbe e2|.
    Only if it is dead will the typechecker allow us to return |e2'|
    without the binding.
    Finally, note that checking liveness \emph{after} already removing dead bindings
    from the body corresponds to \emph{strongly} live variable analysis.

  \paragraph{Correctness}
    We prove preservation of semantics based on the total evaluation function.
    Since we allow functions as values, reasoning about equality
    requires us to postulate extensionality.
    This does not impact the soundness of the proof
    and could be avoided by moving to a different setting,
    such as homotopy type theory \cite{Univalent2013HomotopyTypeTheory}.
    \begin{code}
      postulate
        extensionality :
          {S : Set} {T : S -> Set} {f g : (x : S) -> T x} ->
          (forall x -> f x == g x) -> f == g
    \end{code}

    As the transformed expression generally has a different context
    than the input expression,
    they cannot be evaluated under the same environment.
    We project the environment to match the smaller context,
    dropping all its unneeded elements.
    \begin{code}
      project-Env : Delta C= Gamma -> Env Gamma -> Env Delta
    \end{code}
    \begin{code}
      dbe-correct :
        (e : Expr sigma Gamma) (env : Env Gamma) ->
        let e' ^ theta = dbe e
        in eval e' (project-Env theta env) == eval e env
    \end{code}
    Alternatively, it is possible to rename the expression
    (and |law-eval-rename-Expr| witnesses that both approaches are exchangable),
    but in this case it turns out to be more convenient to reason about context projection.
    \begin{code}
      law-eval-rename-Expr :
        (e : Expr sigma Delta) (theta : Delta C= Gamma) (env : Env Gamma) ->
        eval (rename-Expr theta e) env == eval e (project-Env theta env)
    \end{code}

    The inductive proof requires combining a large number of laws about
    evaluation, renaming, environment projection and the thinnings we constructed.
    The |Lam| case exemplifies that.
    We omit most of the proof terms except for the inductive hypothesis, as they are rather long.
    The intermediate terms still demonstrate how we need to apply several lemmas.
    \begin{code}
      dbe-correct (Lam e1) env =
        let e1' ^ theta1 = dbe e1
        in extensionality lambda v ->
            eval (rename-Expr (un-pop theta1) e1') (project-Env (os (pop theta1)) (Cons v env))
          ==<[ law-eval-rename-Expr e1' (un-pop theta1) _ ]>
            eval e1' (project-Env (un-pop theta1) (project-Env (os (pop theta1)) (Cons v env)))
          ==<[ (dots (cong (eval e1') (sym (law-project-Env-.. (un-pop theta1) (os (pop theta1)) (Cons v env))))) ]>
            eval e1' (project-Env (un-pop theta1 .. os (pop theta1)) (Cons v env))
          ==<[ (dots (cong (lambda x -> eval e1' (project-Env x (Cons v env))) (law-pop-inv theta1))) ]>
            eval e1' (project-Env theta1 (Cons v env))
          ==<[ dbe-correct e1 (Cons v env) ]>
            eval e1 (Cons v env)
          QED
      (dots)
    \end{code}

    The cases for binary operators have a similar structure,
    but are even longer, as they need to apply laws once for each subexpression.
    Since the implementation uses a \textbf{with}-abstraction for the |Let|-case,
    the proof does the same:
    \begin{code}
      dbe-correct (Let e1 e2) env with dbe e1 | dbe e2 | dbe-correct e1 | dbe-correct e2
      ... | e1' ↑ theta1 | e2' ^ o' theta2 | h1 | h2 =
        h2 (Cons (eval e1 env) env)
      ... | e1' ↑ theta1 | e2' ^ os theta2 | h1 | h2 =
        let v = eval (rename-Expr (un-\/1 theta1 theta2) e1') (project-Env (theta1 \/ theta2) env)
        in
          eval (rename-Expr (os (un-\/2 theta1 theta2)) e2')
            (Cons v (project-Env (theta1 \/ theta2) env))
        ==<[ (dots) ]>
          (dots)      -- long proof
        ==<[ (dots) ]>
          eval e2 (Cons (eval e1 env) env)
        QED
    \end{code}
    Note that we also \textbf{with}-abstract over the inductive hypothesis.
    When abstracting over e.g. |dbe e1|,
    the statement we need to prove gets generalised and then talks about |e1'|.
    However, |dbe-correct e1| talks about |dbe e1| and Agda is not aware of their connection.
    Generalising |dbe-correct e1| makes it refer to |e1'| as well.
    \footnote{\url{https://agda.readthedocs.io/en/v2.6.3/language/with-abstraction.html}}


\subsection{Using Annotations}
\label{sec:de-bruijn-dbe-live}
    In compilers, it is a common pattern to perform
    separate analysis and transformation passes,
    for example with strictness and occurrence analysis in GHC
    \cite{Jones1998TransformationOptimiser}.
    We can do the same to make variable liveness information available
    without repeatedly having to compute it on the fly.
    For dead binding elimination,
    this allows us to avoid the redundant renaming of subexpressions.

  \paragraph{Liveness annotations}
    To annotate each part of the expression with its live variables,
    we first need to define a suitable datatype of annotated expressions
    |LiveExpr tau theta|.
    The thinning |theta| here captures liveness information
    in the same way as during the direct transformation in section
    \ref{sec:de-bruijn-dbe-direct}.
    Its target context |Gamma| plays the same role as in |Expr sigma Gamma|,
    but |Delta| only contains the live variables.
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
          LiveExpr tau (theta1 \l/ theta2)
        Val :
          (interpretU(sigma)) ->
          LiveExpr sigma oe
        Plus :
          {theta1 : Delta1 C= Gamma} {theta2 : Delta2 C= Gamma} ->
          LiveExpr NAT theta1 ->
          LiveExpr NAT theta2 ->
          LiveExpr NAT (theta1 \/ theta2)
    \end{code}
    The operator |_\l/_| used here
    can refer to either one of the two versions we introduced,
    but for the remainder of this thesis we will use the strongly live version.

  \paragraph{Analysis}
    To create such an annotated expressions, we need to perform
    strongly live variable analysis.
    As we do not know the live variables upfront,
    |analyse| computes an existentially qualified context and thinning,
    together with a matching annotated expression.
    The implementation is straightforward,
    directly following the expression's structure.
    \begin{code}
      analyse : Expr sigma Gamma -> (Exists (Delta) Ctx) (Exists (theta) (Delta C= Gamma)) LiveExpr sigma theta
      analyse (Var {sigma} x) =
        (sigma :: []) , o-Ref x , Var x
      analyse (App e1 e2) =
        let  Delta1 , theta1 , le1 = analyse e1
             Delta2 , theta2 , le2 = analyse e2
        in \/-vars theta1 theta2 , (theta1 \/ theta2) , App le1 le2
      (dots)
    \end{code}

    It is sensible to assume that the only thing analysis does
    is to attach annotations without changing the structure of the expression.
    We capture this property by stating that we can always forget the annotations
    to obtain the original expression (|forget . analyse == id|).
    \begin{code}
      forget : {theta : Delta C= Gamma} -> LiveExpr tau theta -> Expr tau Gamma

      analyse-preserves :
        (e : Expr tau Gamma) ->
        let _ , _ , le = analyse e
        in forget le == e
    \end{code}

    Note that we can evaluate |LiveExpr| directly, differing from |eval| in two points:
    Firstly, since the annotations make it easy to identify dead let-bindings,
    we can skip their evaluation.
    Secondly, evaluation works under any environment containing \emph{at least} the live variables.
    This makes it possible to get by with the minimal required environment,
    but still gives some flexibility.
    For example, we can avoid projecting the environment for each recursive call,
    just manipulating the thinning instead.
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
    % NOTE: If this text about evalLive ever gets removed,
    % we need to move some of it to the explanation of co-de-Bruijn evaluation.

  \paragraph{Transformation}
    The second pass we perform is similar to |dbe| in the direct approach,
    but with a few key differences.
    Firstly, it operates on annotated expressions |LiveExpr tau theta|
    for a known thinning |theta : Delta C= Gamma| instead of discovering the
    thinning and returning it with the result.
    However, the transformed expression will not necessarily be returned in
    the smallest possible context |Delta|, but any chosen larger context |Gamma'|.
    This way, instead of inefficiently having to rename afterwards,
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

    Finally, we can compose analysis and transformation into an operation
    with the same signature as the direct implementation.
    \begin{code}
      dbe : Expr sigma Gamma -> Expr sigma ^^ Gamma
      dbe e = let _ , theta , le = analyse e in transform le oi ^ theta
    \end{code}

  \paragraph{Correctness}
    The goal is again to show that dead binding elimination preserves semantics,
    which we can express with the same statement as before,
    or conceptually as |eval . dbe == eval|.
    We could again immediately attempt a proof by structural induction,
    but each case would require cumbersome massaging
    of the thinnings supplied to various operations.
    Instead, we aim to simplify the proof by breaking it down into smaller parts
    using the optimised semantics:
    \begin{align*}
      \Varid{evalLive} &\equiv \Varid{eval} \circ \Varid{forget}   \\
      \Varid{evalLive} &\equiv \Varid{eval} \circ \Varid{transform}
    \end{align*}
    Both proofs work inductively on the expression,
    with most cases being a straightforward congruence.
    The interesting one is again |Let|,
    where we split cases on the variable being used or not
    and need some auxiliary facts about evaluation, renaming and contexts.

    After doing two relatively simple proofs,
    we can combine them and do the remaining reasoning
    without having to handle each constructor separately.
    Conceptually, we pre-compose |analyse| on both sides and remove
    |forget . analyse| (which we know forms an identity)
    to obtain the desired equality.
    \begin{align*}
      &\Varid{eval} \circ \Varid{transform}&
      &\equiv&
      &\Varid{eval} \circ \Varid{forget}
      \\
      &\Varid{eval} \circ \Varid{transform} \circ \Varid{analyse}&
      &\equiv&
      &\Varid{eval} \circ \Varid{forget} \circ \Varid{analyse}
      \\
      &\Varid{eval} \circ \Varid{dbe}&
      &\equiv&
      &\Varid{eval}
    \end{align*}

    Just as |transform| itself,
    the proof statements in Agda are generalised
    to evaluation under any |Env Gamma'|,
    as long as it contains the live variables.
    This gives us more flexibility when using the inductive hypothesis,
    showing that it can sometimes be easier to prove something more general.

\section{Let-sinking}
\label{sec:de-bruijn-let-sinking}
    As outlined in section \ref{sec:program-transformations},
    we want to move a single let-bindings as far inward as possible
    without duplicating it or pushing it into a $\lambda$-abstraction.
    Again, we will first show a direct implementation and then employ
    the annotated expression type.

\subsection{Direct Approach}
\label{sec:de-bruijn-let-sinking-direct}
  \paragraph{Type signature}
    We want to replace a let-binding |Let decl e|
    with the result of the transformation |sink-let decl e|,
    which suggests a signature like
    |sink-let : Expr sigma Gamma -> Expr tau (sigma :: Gamma) -> Expr tau Gamma|.
    However, while we initially deal with the topmost entry in the context,
    this changes when going under other binders.
    The solution chosen here uses list concatenation in the context
    to allow |sigma| to occur at any position.
    \begin{code}
      sink-let :
        Expr sigma (Gamma1 ++ Gamma2) ->
        Expr tau (Gamma1 ++ sigma :: Gamma2) ->
        Expr tau (Gamma1 ++ Gamma2)
    \end{code}
    Choosing |[]| as the prefix then again results in the signature above.

  \paragraph{Transformation}
    Just as dead binding elimination, let-sinking heavily relies on variable liveness information.
    To know where a binding should be moved, we need to know where it is used.
    As we are working with a plain (unannotated) syntax tree in this section,
    we need to query the subexpressions' variable usage on demand,
    which repeatedly traverses the expression.
    This is difficult to avoid, since usage information is computed bottom-up,
    but let-sinking needs to proceed top-down.

    More concretely, we need to find out for each subexpression
    whether it uses the binding we are let-sinking or not.
    If the binding is unused, we need to make that clear to the typechecker
    by removing it from the subexpression's context.
    Therefore, we combine querying and the context change into a single operation
    we refer to as \emph{strengthening}.
    \begin{code}
      strengthen :  Expr tau (Gamma1 ++ sigma :: Gamma2) -> Maybe (Expr tau (Gamma1 ++ Gamma2))
    \end{code}

    We now give the complete implementation of let-sinking
    before highlighting specific parts.
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
        Let decl (rename-top e) -- Do not sink into $\lambda$-abstractions!
      sink-let decl (At(e)(Let e1 e2)) with strengthen e1 | strengthen e2
      ... | just e1'  | just e2'  = Let e1' e2'
      ... | nothing   | just e2'  = Let (sink-let decl e1) e2'
      ... | just e1'  | nothing   = Let e1' (sink-let (weaken decl) e2)
      ... | nothing   | nothing   = Let decl (rename-top e)
      sink-let decl (Val v) =
        Val v
      sink-let decl (At(e)(Plus e1 e2)) with strengthen e1 | strengthen e2
      ... | just e1'  | just e2'  = Plus e1' e2'
      ... | nothing   | just e2'  = Plus (sink-let decl e1) e2'
      ... | just e1'  | nothing   = Plus e1' (sink-let decl e2)
      ... | nothing   | nothing   = Let decl (rename-top e)
    \end{code}

  \paragraph{Variables}
    When sinking a binding into a variable, there are two possible cases:
    \begin{enumerate}
      \item If the variable references exactly the let-binding we are sinking,
        we can replace it by the declaration,
        effectively inlining it.
      \item If the variable references a different element of the context,
        the declaration is unused
        and we  only need to rename the variable into the smaller context.
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
    Once we stop sinking the let-binding (e.g. when we reach a $\lambda$-abstraction),
    we insert the declaration.
    However, the typechecker will not accept a plain |Let decl e|.
    It is still necessary to rename the expression,
    since it makes use of the newly created binding,
    but expects it at a different de Bruijn index.
    \begin{code}
      rename-top : Expr tau (Gamma1 ++ sigma :: Gamma2) -> Expr tau (sigma :: Gamma1 ++ Gamma2)
    \end{code}

  \paragraph{Binary constructors}
    For binary operators, we need to check which subexpressions make use of the declaration.
    There are four possible cases:
    \begin{enumerate}
      \item
        Both of the subexpressions can be strengthened.
        This means that we are sinking a dead let-binding,
        which normally should not happen.
        Nevertheless, we need to handle the case,
        simply dropping the binding.
      \item
        The right subexpression can be strengthened.
        We recurse into the left one.
      \item
        The left subexpression can be strengthened.
        We recurse into the right one.
      \item
        Neither subexpression can be strengthened, as both use the declaration.
        To avoid duplicating code, we do not sink further,
        but create a let-binding at the current location.
    \end{enumerate}

  \paragraph{Binders}
    If we recurse into the body of a let-binding,
    an additional variable comes into scope.
    This means that we need to add it to the context prefix |Gamma1|
    and weaken the declaration.
    \begin{code}
      weaken : Expr tau Gamma -> Expr tau (sigma :: Gamma)
      weaken = rename-Expr (o' oi)
    \end{code}
    This traverses the declaration for each binder it is moved across,
    but in the next section we will use a simple trick to avoid that.

\subsection{Using Annotations}
\label{sec:de-bruijn-let-sinking-live}
    Perhaps unsurprisingly, we can again avoid the repeated querying
    using liveness annotations.
    As during dead binding elimination, we first do an analysis pass
    and later simply look at the annotated thinnings
    to find out where a declaration is used.

    The structure of the implementation is the same as for the direct approach,
    so we will only highlight a few differences.

  \paragraph{Type signature}
    Similarly to section \ref{sec:de-bruijn-dbe-live},
    we first perform the analysis and then a transformation
    that results in a plain |Expr| again.
    Combined, this has the same signature as the direct version.
    \begin{code}
      transform :
        {theta : Delta C= (Gamma1 ++ sigma :: Gamma2)} ->
        Expr sigma ^^ (Gamma1 ++ Gamma2) ->
        LiveExpr tau theta ->
        Expr tau (Gamma1 ++ Gamma2)
    \end{code}
    \begin{code}
      sink-let : Expr sigma (Gamma1 ++ Gamma2) -> Expr tau (Gamma1 ++ sigma :: Gamma2)  -> Expr tau (Gamma1 ++ Gamma2)
      sink-let decl e = let _ , theta , le = analyse e in transform (decl ^ oi) le
    \end{code}

    Note that only the body is annotated,
    as we do not need liveness information for the declaration.
    The declaration however is passed with a thinning.
    This change is independent of the others,
    but will avoid repeatedly having to rename the declaration
    when going under binders.

  \paragraph{Binary constructors}
    The |Let| case shows all major changes.
    The main one is that instead of traversing the subexpressions
    (attempting to strengthen them),
    it is sufficient to work with the thinnings found during analysis.
    We make use of the ability to split and concatenate them,
    as shown in section \ref{sec:de-bruijn-thinnings}.
    \begin{code}
      transform {Gamma1 = Gamma1} decl e@(Let {theta1 = theta} {theta2 = phi} e1 e2)
          with Gamma1 -| theta | (_ :: Gamma1) -| phi
      ... | split theta1 (o' theta2) (refl , refl) | split phi1 (o' phi2) (refl , refl) =
        Let (DBE.transform e1 (theta1 ++C= theta2)) (DBE.transform e2 (phi1 ++C= phi2))
      ... | split theta1 (os theta2) (refl , refl) | split phi1 (o' phi2) (refl , refl) =
        Let (transform decl e1) (DBE.transform e2 (phi1 ++C= phi2))
      ... | split theta1 (o' theta2) (refl , refl) | split phi1 (os phi2) (refl , refl) =
        Let (DBE.transform e1 (theta1 ++C= theta2)) (transform (thin^^ (o' oi) decl) e2)
      ... | split theta1 (os theta2) (refl , refl) | split phi1 (os phi2) (refl , refl) =
        Let (rename-Expr^^ decl) (rename-top (forget e))
      (dots)
    \end{code}
    Focusing on the first subexpression,
    we use |_-||_| to split the annotated thinning
    |theta : (Delta1 ++ Delta2) C= (Gamma1 ++ sigma :: Gamma2)|
    from the context of |e1| into two thinnings
    |theta1 : Delta1 C= Gamma1| and
    |theta2 : Delta2 C= sigma :: Gamma2|.
    If the declaration is unused, we obtain a smaller |theta2|,
    which we can use to construct
    |theta1 ++C= theta2 : (Delta1 ++ Delta2) C= (Gamma1 ++ Gamma2)|,
    which shows that |sigma| is not required in the context of |e1|.
    To then turn the annotated |e1| into an |Expr sigma (Gamma1 ++ Gamma2)|,
    we could forget the annotations followed by renaming,
    but we instead use the already defined |DBE.transform|,
    which does the job in a single traversal.

  \paragraph{Binders}
    Instead of weakening the declaration every time we go under a binder,
    we manipulate the thinning it is wrapped in |thin^^ (o' oi)|.
    As a result, we only need to rename the declaration once at the end,
    when the binding is created.
    \begin{code}
      rename-Expr^^ : Expr sigma ^^ Gamma -> Expr sigma Gamma
      rename-Expr^^ (e ^ theta) = rename-Expr theta e
    \end{code}


\section{Discussion}
\label{sec:de-bruijn-discussion}
    We used thinnings to implement live variable analysis and two program transformations.
    In both cases,
    the approach of directly performing the transformation on de Bruijn syntax
    required us to traverse a number of syntax nodes roughly quadratic in the size of the tree.
    At the cost of a single analysis pass upfront (and some additional code),
    we were able to replace the redundant traversals with simple operations on thinnings.

  \paragraph{Reordering the context}
    When changing the order of let-bindings during let-sinking,
    the order of the variables in the context changes as well.
    As thinnings present \emph{order-preserving} embeddings,
    they are not suited to describe such a change of context.
    Consequently, we had to resort to concatenation
    and define an additional set of operations,
    such as for renaming expressions.
    The complexity of the transformation was significantly higher
    than for dead binding elimination.

    We will continue using the order-preserving flavour of thinnings,
    but discuss potential alternatives in chapter
    \ref{ch:discussion}.


\subsection{Alternative Designs}
  \paragraph{Iterating transformations}
    As discussed in section \ref{sec:program-transformations},
    more than one pass of dead binding elimination might be necessary to remove all unused bindings.
    While in our simple setting all these bindings could be identified in a single pass
    using strongly live variable analysis,
    in general it can be beneficial to iterate optimisations
    a fixed number of times or until a fixpoint is reached.
    For example, it is reported that GHC's simplifier pass is iterated up to 4 times
    \cite{Jones1998TransformationOptimiser}.

    As an example, we defined a function that keeps applying |dbe|
    as long as the number of bindings in the expression decreases.
    Such an iteration is not structurally recursive,
    so Agda's termination checker needs our help.
    We observe that the algorithm must terminate,
    since the number of bindings decreases with each iteration (but the last)
    and clearly can never be negative.
    This is an instance of to the ascending chain condition
    in program analysis literature \cite{Nielson1999PrinciplesProgramAnalysis}.
    To convince the termination checker,
    we used the technique of well-founded recursion
    \cite{Bove2014PartialityRecursion}
    on the number of bindings.
    The correctness was then straightforward to prove,
    as it follows directly from the correctness of each individual iteration step.

  \paragraph{Signature of let-sinking}
    We remind ourselves of the type signature of |sink-let|.
    To talk about removing an element from the context at a specific position,
    we used list concatenation.
    \begin{code}
      sink-let :
        Expr sigma (Gamma1 ++ Gamma2) ->
        Expr tau (Gamma1 ++ sigma :: Gamma2) ->
        Expr tau (Gamma1 ++ Gamma2)
    \end{code}
    Note that we could alternatively have used other ways to achieve the same,
    such as insertion at a position |n : Fin (length Gamma)|
    or removal of |sigma| at a position |i : Ref sigma Gamma|.
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
    Using list concatenation, however, seems more principled
    and allows us to make use of general operations and properties
    of the concatenation of contexts and thinnings.

  \paragraph{Keeping annotations}
    In both transformations, we used annotated expressions for the input,
    but returned the result without annotations.
    When performing multiple different transformations in sequence
    (or the same one multiple times),
    each pass requires us to do live variable analysis anew,
    just to then throw away the results.

    If instead transformations computed updated liveness annotations
    as they are constructing the resulting expression,
    we could stay in |LiveExpr| world all the time.
    However, each transformation would then effectively need to include analysis,
    making it more complex.
    This could potentially be factored out,
    but a first attempt for let-sinking encountered various practical issues.
    In addition, indexing |LiveExpr| by \emph{two} different contexts
    seems redundant.
    Could a representation considering only the live variables be simpler,
    while providing the same benefits?
    The next chapter will feature such a representation.
