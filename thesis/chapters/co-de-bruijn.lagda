%include agda.fmt
%include custom.fmt

\chapter{Co-de-Bruijn Representation}
\label{ch:co-de-bruijn}
    After showing that de Bruijn representation can be made type- and scope-correct
    by indexing expressions with their context (the variables in scope),
    we found out how useful it is to also know the live variables.
    The type of annotated expressions we created
    was therefore indexed (perhaps redundantly) by both of these,
    as well as the thinning between them.
    Here however, we will work with McBride's co-de-Bruijn syntax
    \cite{McBride2018EveryBodysGotToBeSomewhere},
    another nameless intrinsically typed representation,
    which is indexed by its weakly live variables alone.

    In this representation,
    bindings can be added or removed without having to traverse their body
    to rename the variables.
    The bookkeeping required is relatively complex,
    but Agda's typechecker helps us maintain the invariants.

    We will begin by giving an intuition for the co-de-Bruijn representation
    and show how it translates into a few core building blocks,
    each with a convenient smart constructor.
    Based on these, we define a co-de-Bruijn-based syntax tree for our expression language
    and demonstrate that it can be converted to and from
    our original de Bruijn expressions.
    Once the foundations are in place,
    we again perform dead binding elimination and let-sinking,
    making use of the variable liveness information inherent in co-de-Bruijn terms.

\section{Intrinsically Typed Syntax}
\label{sec:co-de-bruijn-intrinsically-typed}
  \paragraph{Intuition}
    The intuition that McBride gives
    (and uses to motivate the name \emph{co-de-Bruijn})
    is that de Bruijn representation keeps all introduced bindings in its context
    and only selects one of them \emph{as late as possible},
    when encountering a variable, i.e. de Bruijn index.
    Co-de-Bruijn representation follows the dual approach,
    shrinking down the context \emph{as early as possible}
    to only those variables that occur in the respective subexpression.
    When reaching a variable, only a singleton context remains,
    so there is no need for an index.

    After dealing with live variable analysis in the previous chapter,
    we also think about it in a way similar to liveness annotations:
    starting from the variables, the live variables get collected
    and turned into annotations, bottom-up.

  \paragraph{Relevant pairs}
    The most insightful situation to consider is that of handling
    multiple subexpressions, for example with addition.
    Assuming we have
    |e1 : Expr NAT Delta1| and
    |e2 : Expr NAT Delta2|, each indexed by their live variables,
    how do we construct the syntax node representing $e_1 + e_2$?
    It should be indexed by the smallest |Gamma| with thinnings
    |theta1 : Delta1 C= Gamma| and
    |theta2 : Delta2 C= Gamma|.
    For |LiveExpr|, we specified the resulting context using |_\/_|,
    ensuring that it is the smallest context into which
    we can embed both |Delta1| and |Delta2|.
    Here, we achieve the same using a \emph{cover} of the thinnings
    to ensure that every element of |Gamma| is part of
    |Delta1|, |Delta2|, or both
    (``everybody's got to be somewhere'').
    Fundamentally, we can never construct a |Cover (o' _) (o' _)|.
    \begin{code}
      data Cover : Delta1 C= Gamma -> Delta2 C= Gamma -> Set where
        c's  : Cover theta1 theta2  -> Cover (o' theta1) (os theta2)
        cs'  : Cover theta1 theta2  -> Cover (os theta1) (o' theta2)
        css  : Cover theta1 theta2  -> Cover (os theta1) (os theta2)
        czz  : Cover oz oz
    \end{code}

    As each binary operator will in some form contain
    two thinnings and their cover,
    we combine them into a reusable datatype called \emph{relevant pair}.
    \begin{code}
      record _><R_ (S T : List I -> Set) (Gamma : List I) : Set where
        constructor pairR
        field
          outl   : S ^^ Gamma    -- containing |S Delta1| and |Delta1 C= Gamma|
          outr   : T ^^ Gamma    -- containing |T Delta2| and |Delta2 C= Gamma|
          cover  : Cover (thinning outl) (thinning outr)
    \end{code}

    As an example, let us construct the relevant pair of the two expressions
    |e1 : Expr NAT (sigma :: [])| and |e2 : Expr NAT (tau :: [])|,
    each with a (different) single live variable in their context.
    The combined live variables then contain both variables,
    so one thinning will target the first element, and one the other:
    |pairR (e1 ^ os (o' oz)) (e2 ^ o' (os oz)) c : (Expr NAT ><R Expr NAT) (sigma :: tau :: [])|.
    The cover |c = cs' (c's czz)| follows the same structure.

    Manually finding the combined live variables and constructing the cover
    everytime a relevant pair gets constructed quickly gets cumbersome.
    We can delegate the work to a smart constructor,
    but note that nothing about |e1| and |e2| tells us
    which element should come first in the context
    -- the choice was made (arbitrarily) by creating the thinnings.
    As part of the input, we therefore require thinnings into a shared context.
    Any shared context will do,
    since we only need it to relate the two subexpressions' contexts
    and can still shrink it down to the part that is live.
    \begin{code}
      _,R_ : S ^^ Gamma -> T ^^ Gamma -> (S ><R T) ^^ Gamma
    \end{code}
    We will not show the implementation here,
    but it is generally similar to that of |_\/_|,
    recursing over each element of |Gamma| to check which of the thinnings use it,
    decide whether to include it in the resulting context,
    and construct the matching thinnings and cover.

  \paragraph{Bindings}
    Another important consideration are bindings.
    Not all bound variables are required to be used,
    they can be dropped from the context of their subexpressions immediately.
    For example, $\lambda$-abstractions that don't use their argument are perfectly valid
    and cannot be removed as easily as dead let-bindings.

    With the goal of creating another general building block
    that can be used for a wide range of language constructs,
    we allow a list of multiple simultaneous bindings.
    Instead of an operation like |pop| dealing with a single binding,
    we now use a thinning |phi  : Delta' C= Gamma'|
    to express which of the bound variables |Gamma'| are used,
    and concatenate the live variables |Delta'| to the context.

    \begin{code}
      record _|-_ (Gamma' : List I) (T : List I -> Set) (Gamma : List I) : Set where
        constructor _\\_
        field
          {Delta'}  : List I
          thinning  : Delta' C= Gamma'
          thing     : T (Delta' ++ Gamma)
    \end{code}

    Given an expression, wrapping it into this datatype
    requires us to find out which part of its context is bound here.
    Luckily, with the right thinning at hand,
    this can be handled by a general smart constructor.

    \begin{code}
      _\\R_ : (Gamma' : List I) -> T ^^ (Gamma' ++ Gamma) -> (Gamma' |- T) ^^ Gamma
    \end{code}
    Again, we will not spend much time explaining the implementation,
    but briefly mention that it relies on the ability to split the thinning
    that goes into |Gamma' ++ Gamma| into two parts using |_-||_|,
    as seen in section \ref{sec:de-bruijn-thinnings}.


  \paragraph{Expression language}
    Using the building blocks defined above,
    our expression language can be defined pretty concisely.

    \begin{code}
      data Expr : (sigma : U) (Gamma : Ctx) -> Set where
        Var   : Expr sigma (sigma :: [])
        App   : (Expr (sigma => tau) ><R Expr sigma) Gamma -> Expr tau Gamma
        Lam   : ((sigma :: []) |- Expr tau) Gamma -> Expr (sigma => tau) Gamma
        Let   : (Expr sigma ><R ((sigma :: []) |- Expr tau)) Gamma -> Expr tau Gamma
        Val   : (interpretU(sigma)) -> Expr sigma []
        Plus  : (Expr NAT ><R Expr NAT) Gamma -> Expr NAT Gamma
    \end{code}

    Let-bindings make use of both a relevant pair and binding,
    without us having to think much about what the thinnings involved should look like.
    Since the context of the declaration is considered relevant
    irrespective of the let-binding itself being live,
    it corresponds to the \emph{weakly} live variables.
    Achieving \emph{strong} variable liveness would require a custom combinator,
    but more importantly, we will show that it is not necessary
    for an efficient implementation of the strong version of dead binding elimination.

  \paragraph{Evaluation}
    To later be able to talk about preservation of semantics,
    we first need to define a semantics,
    which we again do in form of a total evaluation function.
    % Since the expressions' context gets shrunk down at each node,
    % we either need to project the matching part out of the environment at each recursive call
    % or maintain a thinning from the required live variables to the larger context
    % the environment provides.
    % We choose the latter option, as we prefer to manipulate thinnings where possible.
    As with |evalLive|,
    we allow supplying an environment that is larger than strictly needed.
    This allows us to compose a thinning
    instead of having to project the environment for each recursive call.

    \begin{code}
      eval : Expr tau Delta -> Delta C= Gamma -> Env Gamma -> (interpretU(tau))
      eval Var theta env =
        lookup (ref-o theta) env
      eval (App (pairR (e1 ^ theta1) (e2 ^ theta2) cover)) theta env =
        eval e1 (theta1 .. theta) env
          (eval e2 (theta2 .. theta) env)
      eval (Lam (psi \\ e)) theta env =
        lambda v -> eval e (psi ++C= theta) (Cons v env)
      eval (Let (pairR (e1 ^ theta1) ((psi \\ e2) ^ theta2) c)) theta env =
        eval e2 (psi ++C= (theta2 .. theta))
          (Cons (eval e1 (theta1 .. theta) env) env)
      (dots)
    \end{code}

    At the variable occurrences, the expression's context is a singleton
    and we can convert the thinning into an index (|Ref|)
    to do a lookup on the environment.
    The thinning |psi| for bindings that get introduced needs to concatenated
    with the accumulated binding.
    Finally note that despite all the similarities to |evalLive|,
    we do not skip the declaration's evaluation
    when encountering a dead let-binding.


\section{Conversion from/to de Bruijn Syntax}
\label{sec:co-de-bruijn-conversion}
    The conversion between de Bruijn and co-de-Bruijn representation
    is very similar to computing and forgetting annotations
    in the second part of section \ref{sec:de-bruijn-dbe}.

  \paragraph{To de Bruijn}
    Since the converted expression often needs to be placed in a larger context
    than just its live variables,
    we allow to specify the desired context using a thinning.
    \begin{code}
      toDeBruijn :  Delta C= Gamma -> CoDeBruijn.Expr sigma Delta -> DeBruijn.Expr sigma Gamma
    \end{code}
    The recursive calls work the exact same way as during evaluation,
    composing the thinning on the way down
    to turn it into into a de Bruijn index when reaching a variable.
    The only difference is that instead of computing a value,
    the resulting expressions are just packaged up into a syntax tree again.

  \paragraph{From de Bruijn}
    The other direction is slightly more work,
    as it effectively needs to perform live variable analysis.
    Luckily, we benefit greatly from the smart constructors.
    As we do not know the context of the resulting co-de-Bruijn expression upfront,
    we once more return the result with a thinning.
    \begin{code}
      fromDeBruijn : DeBruijn.Expr sigma Gamma -> CoDeBruijn.Expr sigma ^^ Gamma
      fromDeBruijn (Var x) =
        Var ^ o-Ref x
      fromDeBruijn (App e1 e2) =
        map^^ App (fromDeBruijn e1 ,R fromDeBruijn e2)
      fromDeBruijn (Lam e) =
        map^^ Lam (_ \\R fromDeBruijn e)
      fromDeBruijn (Let e1 e2) =
        map^^ Let (fromDeBruijn e1 ,R (_ \\R fromDeBruijn e2))
      fromDeBruijn (Val v) =
        Val v ^ oe
      fromDeBruijn (Plus e1 e2) =
        map^^ Plus (fromDeBruijn e1 ,R fromDeBruijn e2)
    \end{code}
    After using the smart constructors
    to obtain a relevant pair or binder (with a thinning),
    it only remains to wrap things up using the right constructor.

  \paragraph{Correctness}
    While the conversion is pretty straightforward,
    mapping constructors one-to-one to their counterparts,
    we can prove that the semantics of the two representations agree.
    \begin{code}
      toDeBruijn-correct :
        (e : CoDeBruijn.Expr tau Delta) (env : Env Gamma) (theta : Delta C= Gamma) ->
        let e' = toDeBruijn theta e
        in DeBruijn.eval e' env == CoDeBruijn.eval e theta env
    \end{code}
    \begin{code}
      fromDeBruijn-correct :
        (e : DeBruijn.Expr tau Gamma) (env : Env Gamma) ->
        let e' ^ theta = fromDeBruijn e
        in CoDeBruijn.eval e' theta env == DeBruijn.eval e env
    \end{code}
    The first proof works by a completely straightforward structural induction,
    without requiring any further lemmas.
    The other direction is slightly more interesting:
    As the smart constructors are defined using \textbf{with}-abstraction,
    the case for each constructor first requires us to mirror that structure
    before being able to use the induction hypothesis.
    \pagebreak

\section{Dead Binding Elimination}
\label{sec:co-de-bruijn-dbe}
    Co-de-Bruijn expressions enforce that every variable in their context
    must occur somewhere.
    However, there can still be dead let-bindings:
    the declaration of type |sigma| bound by |psi \\ e2 : ((sigma :: []) ||- Expr tau) Gamma|
    can be immediately discarded in |psi|,
    never to occur in |e2|.
    We need to identify such dead let-bindings and eliminate them.

    Since an expression's context contains its \emph{weakly} live variables
    and removing dead bindings can make some of them dead,
    we return the result in a (generally) smaller context with a thinning.

    \begin{code}
      dbe : Expr tau Gamma -> Expr tau ^^ Gamma
    \end{code}

  \paragraph{Transformation}
    The weakly live variables
    are already present as part of the co-de-Bruijn representation,
    so no further analysis is necessary.
    For the weak version of dead binding elimination,
    we simply need to find all let-bindings in the input expression
    that have a thinning |o' oz : [] C= (sigma :: [])|.

    The change in context caused by the transformation
    has several consequences:
    Firstly, these new thinnings coming from each recursive call
    need to be composed with the existing ones on the way up (e.g. using |thin^^|).
    Secondly, we need to rebuild the variable usage information,
    i.e. calculate new contexts and covers at each node
    using the smart constructors |_\\R_| and |_,R_|.
    \begin{code}
      dbe : Expr tau Gamma -> Expr tau ^^ Gamma
      dbe Var =
        Var ^ oi
      dbe (App (pairR (e1 ^ phi1) (e2 ^ phi2) c)) =
        map^^ App (thin^^ phi1 (dbe e1) ,R thin^^ phi2 (dbe e2))
      dbe (Lam (psi \\ e)) =
        map^^ (Lam . thin|- psi) (_ \\R dbe e)
      dbe (Let (pairR (e1 ^ phi1) ((o' oz \\ e2) ^ phi2) c)) =
        thin^^ phi2 (dbe e2)
      dbe (Let (pairR (e1 ^ phi1) ((os oz \\ e2) ^ phi2) c)) =
        map^^ Let (thin^^ phi1 (dbe e1) ,R thin^^ phi2 (_ \\R dbe e2))
      dbe (Val v) =
        Val v ^ oz
      dbe (Plus (pairR (e1 ^ phi1) (e2 ^ phi2) c)) =
        map^^ Plus (thin^^ phi1 (dbe e1) ,R thin^^ phi2 (dbe e2))
    \end{code}
    \begin{code}
      thin|- : Gamma1 C= Gamma2 -> (Gamma1 |- T) Gamma -> (Gamma2 |- T) Gamma
      thin|- phi (theta \\ t) = (theta .. phi) \\ t
    \end{code}

    To get the strong version,
    we can do the recursive calls first and check the thinnings \emph{afterwards}.
    For that we use a small helper function |Let?|,
    which behaves like the constructor |Let| if the binding is live,
    but otherwise removes the declaration.
    The other cases are the same as in the previous section.
    \begin{code}
      Let? : (Expr sigma ><R ((sigma :: []) |- Expr tau)) Gamma -> Expr tau ^^ Gamma
      Let? (At(p)(pairR _ ((o' oz \\ e2)  ^ theta2)  _)) = e2 ^ theta2
      Let? (At(p)(pairR _ ((os oz \\ _)   ^ _)       _)) = Let p ^ oi
    \end{code}
    \begin{code}
      dbe (Let (pairR (e1 ^ phi1) ((psi \\ e2) ^ phi2) c)) =
        bind^^ Let?
          (thin^^ phi1 (dbe e1) ,R thin^^ phi2 (map^^ (thin|- psi) (_ \\R dbe e2)))
    \end{code}

    Due to the combinators applying and mapping over thinnings,
    the definition is concise, but opaque.
    To give a better feeling for how much plumbing is involved,
    we can also inline all combinators and compose the thinnings manually:
    \begin{code}
      dbe (Let (pairR (e1 ^ phi1) ((psi \\ e2) ^ phi2) c)) =
        let  e1'            ^ phi1'  = dbe e1
             (psi' \\ e2')  ^ phi2'  = _ \\R dbe e2
             p' ^ theta   = (e1' ^ (phi1' .. phi1)) ,R (((psi' .. psi) \\ e2') ^ (phi2' .. phi2))
             e' ^ theta'  = Let? p'
        in
          e' ^ (theta' .. theta)
    \end{code}
    Additionally inlining the smart constructors
    to show how they construct their thinnings
    would make the code even more noisy and difficult to follow.

  \paragraph{Correctness}
    As seen in the inlined version,
    a lot of nontrivial operations are involved in constructing
    the thinnings and covers in the result.
    This also makes the proofs more complicated.
    Often, conceptually simple parts of the proof require
    extensive massaging of deeply buried thinnings
    using commutative laws or helpers with types like
    |theta1' .. theta1 == theta2' .. theta2 -> theta1' .. (theta1 .. phi) == theta2' .. (theta2 .. phi)|.

    \begin{code}
      dbe-correct :
        (e : Expr tau Delta) (env : Env Gamma) (theta : Delta C= Gamma) ->
        let e' ^ theta' = dbe e
        in eval e' (theta' .. theta) env == eval e theta env
    \end{code}

    While the combinators and smart constructors used in the implementation
    compose seamlessly, the same is not quite true for proofs about them.
    We were able to factor out lemmas dealing with |_||-_| and |_><R_|,
    such that e.g. the cases for application and addition in |dbe-correct|
    are both instances of the same proof, using either |_S_| or |_+_| as an argument.
    However, defining these building blocks in a way that allowed composing them
    to handle |Let| proved more difficult than expected.
    In the end, we simply handled |Let| as a similar but separate special case.
    The main issue for proof composability seems to be
    that some type equalities need to be matched on
    (e.g. using \textbf{with}-abstraction)
    just for the required call to the lemma or induction hypothesis to typecheck.
    Some attempts to break the proof into components
    also failed to satisfy the termination checker.

    For let-bindings in the strong version,
    we additionally made use of a lemma stating that
    |Let? p| and |Let p| are semantically equivalent.
    % \begin{code}
    %   lemma-Let? :
    %     (p : (Expr sigma ><R ((sigma :: []) |- Expr tau)) Delta) (env : Env Gamma) (theta : Delta C= Gamma) ->
    %     let e' ^ theta' = Let? p
    %     in eval e' (theta' .. theta) env == eval (Let p) theta env
    % \end{code}

\section{Let-sinking}
\label{sec:co-de-bruijn-let-sinking}
    In addition to the expected benefits
    of readily available variable liveness information,
    we will see that co-de-Bruijn representation also affords us more precision
    when specifying the inputs to the transformation.
    On the flipside, the reordering of the context inherent to let-sinking
    causes even more complications than in the de Bruijn version.

  \paragraph{Type signature}
    We again start from the observation that the signature for let-sinking
    should be similar to the |Let| constructor,
    but allowing for a prefix in context that we need when going under binders.
    But here, declaration and binding form a relevant pair,
    each in their own context with a thinning into the overall context.
    To make it clear what this type consists of, we flatten the structure:
    \begin{code}
      sink-let :
        (decl : Expr sigma ^^ (Gamma1 ++ Gamma2)) ->
        (body : Expr tau ^^ (Gamma1 ++ sigma :: Gamma2)) ->
        Cover (thinning decl) (thinning body) ->
        Expr tau (Gamma1 ++ Gamma2)
    \end{code}
    For now, we will ignore the cover and return the result with a thinning
    (i.e. without having to show that the whole context |Gamma1 ++ Gamma2| is relevant).
    As we will see later, this avoids complicated reasoning about covers.
    \begin{code}
      sink-let :
        Expr sigma ^^ (Gamma1 ++ Gamma2) ->
        Expr tau ^^ (Gamma1 ++ sigma :: Gamma2) ->
        Expr tau ^^ (Gamma1 ++ Gamma2)
    \end{code}

    However, this type is imprecise in a different way:
    The context of the body is thinned into a precisely specified overall context,
    but its own structure is opaque.
    We know that it consists of two parts
    (thinned into |Gamma1| and |Gamma2| respectively),
    but that information first needs to be discovered.
    Furthermore, we want to require that the declaration is live in the body
    we want to move it into, so we know even more about the context.
    To make that structure more apparent,
    we can make stronger assumptions about the context of the body
    (not just the context it is thinned into).
    The structure of the overall context on the other hand is less important to us.
    \begin{code}
      sink-let :
        Expr sigma ^^ Gamma ->
        Expr tau (Gamma1 ++ sigma :: Gamma2) ->
        Gamma1 ++ Gamma2 C= Gamma ->
        Expr tau ^^ Gamma
    \end{code}
    The knowledge that the binding is used eliminates some edge cases
    we previously had to deal with.
    Using a simple wrapper, we can still get back the less restrictive type signature
    that can be applied to any let-binding:
    \begin{code}
      sink-let-top : (Expr sigma ><R ((sigma :: []) |- Expr tau)) Gamma -> Expr tau ^^ Gamma
      sink-let-top (pairR (decl ^ phi) ((os oz \\ e) ^ theta) c) =
        sink-let [] _ (decl ^ phi) e refl theta
      sink-let-top (pairR decl ((o' oz \\ e) ^ theta) c) =
        e ^ theta   -- binding is unused, why bother with let-sinking?
    \end{code}

  \paragraph{Variables}
    We immediately observe this when dealing with variables.
    Since we know that a variable's context contains exactly one element,
    and also that the declaration is part of that of the context,
    the variable \emph{must} refer to the declaration.
    After making this clear to Agda using a pattern match with an absurd case,
    we can replace the variable with the declaration.

  \paragraph{Creating the binding}
    As in the de Bruijn setting, we need to rename the body of the newly created binding.
    However, it becomes more cumbersome here:
    \begin{code}
      reorder-Ctx :
        Expr tau Gamma -> (Gamma == Gamma1 ++ Gamma2 ++ Gamma3 ++ Gamma4) ->
        Expr tau (Gamma1 ++ Gamma3 ++ Gamma2 ++ Gamma4)
    \end{code}
    The context is split into four segments (where |Gamma3| is |(sigma :: [])|) that get reordered,
    which means that we also need to split every thinning and cover into four parts
    and carefully reassemble them.
    \begin{code}
      cover++C=4 :
        (theta1 : Gamma1'  C= Gamma1) (theta2 : Gamma2'  C= Gamma2) (dots) ->
        Cover (theta1 ++C= theta2 ++C= theta3 ++C= theta4) (phi1 ++C= phi2 ++C= phi3 ++C= phi4) ->
        Cover (theta1 ++C= theta3 ++C= theta2 ++C= theta4) (phi1 ++C= phi3 ++C= phi2 ++C= phi4)
    \end{code}
    The need for such an operation suggests that co-de-Bruijn representation,
    and in particular the notion of thinnings it is based on,
    might not be very well suited for the reordering of bindings.

  \paragraph{Binary constructors}
    Variable usage information is immediately available:
    We split and examine the thinnings of the subexpressions to see where the declaration is used.
    Using the cover, we can rule out the case where no subexpression uses the declaration.
    In contrast to the previous implementation of let-sinking,
    no strengthening is necessary: discovering that a variable is unused is enough.
    The subexpressions are then combined using |_,R_|, creating new thinnings and a cover for us.

  \paragraph{Binders}
    No weakening of the declaration is necessary when going under a binder,
    as we simply update its thinning.
    But recursing into the body of another let-binding still complicates things:
    Although we know that the liveness of the bound variable should be unaffected by let-sinking,
    the imprecise type signature allows for changes in context,
    so we need to find out again whether the binding is used or not.

  \paragraph{Correctness}
    Work on the proof is incomplete, as the sheer number of
    operations and bindings involved makes it messy.
    There are many lemmas about splitting thinnings and reordering the context
    that are cumbersome to state and prove correct.
    It seems like some of the complications could be avoided
    if we managed to avoid the usage of |_,R_| as explained in
    section \ref{sec:co-de-bruijn-alternative-designs}.


\section{Discussion}
\label{sec:co-de-bruijn-discussion}
  \paragraph{Useful properties}
    Co-de-Bruijn expressions generally seem promising for defining transformations,
    with several useful properties:
    \begin{enumerate}
      \item Liveness information is present at each syntax node.
      \item Changing the context in a way expressible with thinnings does not require a traversal of the expression.
      \item The type of an expression only depends on the expression itself, not on the (potentially unused) bindings around it.
        One situation where this can be useful is when identifying identical expressions in different parts of the expression,
        as is needed for common subexpression elimination.
    \end{enumerate}
  \paragraph{Complications}
    On the other hand,
    the elaborate bookkeeping that is part of co-de-Bruijn syntax trees
    makes the construction of expressions more complicated.
    While this complexity can be hidden behind smart constructors,
    it leaks easily.
    For example, the proofs about transformed expressions
    are significantly more complex than their de Bruijn counterparts,
    which especially became apparent for let-sinking.
    It might be possible to create a general set of proof combinators
    that mirror the structure of the smart constructors,
    but this kind of abstraction over proofs is usually difficult (or impossible) to achieve.

\subsection{Alternative Designs}
\label{sec:co-de-bruijn-alternative-designs}
  \paragraph{Covers}
    As hinted at when choosing a type signature
    for the let-sinking transformation
    in section \ref{sec:co-de-bruijn-let-sinking},
    it should not be necessary to return the result with a thinning.
    If all variables occur in either declaration or body, they will still occur in the result,
    no matter where exactly the declaration is moved.
    Therefore, the context should always remain the same,
    just the thinnings and covers have to be rebuilt.
    This could potentially simplify parts of the implementation and especially the proof,
    since directly constructing a relevant pair creates fewer indirections
    than using |_,R_| to discover new thinnings.

    It seems desirable to reflect this observation in the type signature,
    specifying the result more precisely.
    However, making it clear to the typechecker
    involves relatively complex manipulation of the covers.

    The issue boils down to quite fundamental associative and commutative
    operations on relevant pairs:
    we want to be able to turn any |(S ><R (T ><R U)) Gamma|
    into |((S ><R T) ><R U) Gamma| or also |(T ><R (S ><R U)) Gamma| etc.,
    and intuitively it's clear that the live variables |Gamma| are unaffected
    by these operations.
