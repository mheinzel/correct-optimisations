\documentclass[sigplan,review]{acmart}

% workaround, see https://github.com/kosmikus/lhs2tex/issues/82
\let\Bbbk\undefined

%include agda.fmt
%include custom.fmt

% https://icfp24.sigplan.org/

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{stmaryrd}
\usepackage{listings}
\usepackage{xcolor}
\usepackage{xspace}
\usepackage{natbib}

\usepackage{todonotes}
\newcommand{\Outline}[1]{\todo[inline,color=gray!30]{#1}}
\newcommand{\Copied}[1]{{\color{gray} #1}}
\newcommand{\TODO}[1]{\todo[inline,color=red!30]{TODO: #1}}

\newcommand{\ValTrue}{\texttt{true}}
\newcommand{\ValFalse}{\texttt{false}}
\newcommand{\Let}[1]{\textbf{let } #1 = }
\newcommand{\LetB}{\textbf{let }} % using de Bruijn indices
\newcommand{\In}{\textbf{ in }}
\newcommand{\Lam}[1]{\lambda #1 .\ }
\newcommand{\DeBruijn}[1]{\langle #1 \rangle}

\acmConference[TyDe ’24]{Workshop on Type-Driven Development}{September 2, 2024}{Milan, Italy}

\begin{document}

% TODO
\title{Provingly Correct Optimisations on Intrinsically Typed Expressions}

\author{Matthias Heinzel}
\affiliation{%
  \institution{Well-Typed LLP}
  \city{London}
  \country{United Kingdom}}
\email{matthias@@well-typed.com}

\author{Wouter Swierstra}
\affiliation{%
  \institution{Utrecht University}
  \city{Utrecht}
  \country{Netherlands}}
\email{w.s.swierstra@@uu.nl}

\begin{abstract}
  \Outline{abstract}
\end{abstract}

\keywords{Intrinsically Typed Syntax, Dependent Types, Agda}

\maketitle

\section{Introduction}
  \Outline{bindings are a challenge for compiler correctness}
    When writing a compiler for a programming language,
    an important consideration is the treatment of binders and variables.
    They are part of most languages and
    there are several options for representing them,
    each with different implications for operating on and reasoning about programs.
    Often, it is possible to represent ill-formed syntax trees
    where variables do not refer to a suitable binding.
    This makes it easy to introduce compiler bugs that change the meaning of a program
    or make it invalid.

    When using a dependently typed programming language such as Agda
    \cite{Norell2008Agda},
    intrinsically typed syntax trees can be used to
    make such ill-formed programs unrepresentable.
    Using this well-known technique,
    expressions become scope- and type-correct by construction,
    allowing for a total evaluation function
    \cite{Augustsson1999WellTypedInterpreter}.
    Intrinsically typed constructions have featured in several papers,
    exploring basic operations like renaming and substitution
    \cite{Allais2018UniverseOfSyntaxes}
    as well as compilation to different target languages
    \cite[online supplementary material]{Pickard2021CalculatingDependentlyTypedCompilers}.

    At the same time, there are large classes of important transformations
    that have not yet received much attention in an intrinsically typed setting.
    Optimisations, for example, play a central role in practical compilers,
    but establishing their correctness is often not trivial,
    with ample opportunity for binding-related mistakes
    \cite{SpectorZabusky2019EmbracingFormalizationGap,Maclaurin2022Foil}.
    Letting the type checker keep track of invariants
    promises to remove common sources of bugs.
    A mechanised proof of semantics preservation can further increase
    confidence in the transformation's correctness.

  \Outline{describe language}
    As a running example, we will consider a simple expression language
    based on the $\lambda$-calculus
    \cite{Barendregt1985LambdaCalculus}.
    On top of variables $\{ x, y, z, a, b, c, f, g, \ldots \}$, function application and $\lambda$-abstraction,
    it has let-bindings, primitive values $v \in \mathbb{B} \cup \mathbb{N}$ (with $\mathbb{B} = \{ \ValTrue , \ValFalse \}$) and a binary addition operator.
    Since we are primarily concerned with variables and binders,
    the choice of possible values and primitive operations on them is mostly arbitrary and can easily be extended.
    \begin{align*}
      P, Q ::=&\ x
      \\ \big||&\ P\ Q
      \\ \big||&\ \lambda x.\ P
      \\ \big||&\ \textbf{let } x = P \textbf{ in } Q
      \\ \big||&\ v
      \\ \big||&\ P + Q
    \end{align*}
    To reduce the number of required parentheses,
    we give function application the highest
    and let-bindings the lowest precedence.

  \Outline{why let-bindings?}
    Let-bindings allow to bind a declaration $P$ to a variable $x$.
    While any let-binding $\Let{x} P \In Q$ can be emulated
    using an immediately applied $\lambda$-abstraction $(\lambda x.\ Q)\ P$,
    they are very common and can benefit
    from transformations that target them specifically.
    For simplicity, we omit further constructs such as branching operators,
    recursive bindings or a fixpoint operator.
    % TODO: discuss extensions?
    %but discuss some potential additions and their implications
    %at the end (section \ref{sec:further-work-extending-language}).

  \Outline{choice of optimisations}
  \TODO{justify focus on functional languages?}
    A large number of program analyses and optimisations are presented in the literature
    \cite{Nielson1999PrinciplesProgramAnalysis,Santos1995CompilationByTransformation}
    and used in production compilers such as the Glorious Haskell Compiler (GHC).
    As an example of a transformation dealing with variables and binders,
    we focus on \emph{dead binding elimination} (DBE).
    Further transformations are briefly discussed in section
    \ref{sec:other-transformations}.

  \Outline{describe DBE}
  \Copied{
    An expression is not forced to make use of all bindings to which it has access.
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
  }

  \Outline{variable liveness}
  \Copied{
    Such dead bindings can be identified by \emph{live variable analysis}
    and consequently be removed.

    A crucial aspect is that of \emph{variable liveness}.
    Whether it is safe to apply a binding-related transformation
    usually depends on which parts of the program make use of which binding.
    We employ several ways of providing and using variable liveness information
    for program transformations.
  }

  \Outline{we consider strongly live variables}
  \Copied{
    Note that $y$ is not needed either: Removing $z$ will make $y$ unused.
    Therefore, multiple iterations of live variable analysis and binding elimination
    might be required to remove as many bindings as possible.
    Alternatively, \emph{strongly live variable analysis} can achieve the same result in a single pass
    by ignoring variable occurrences in the declaration of variables
    unless that variable is live itself.
  }

  \Outline{problems with transformations on de Bruijn}
  \Copied{
    With \emph{de Bruijn indices}
    \cite{DeBruijn1972NamelessIndices},
    one can instead adopt a \emph{nameless} representation.
    Each variable is represented as a natural number,
    counting the number of nested bindings between variable occurrence and its binding:
    $\DeBruijn{0}$ refers to the innermost binding, $\DeBruijn{1}$ to the next-innermost etc.
    If we adapt the syntax for let-bindings to omit the unnecessary variable name,
    the example expression from dead binding elimination is represented as follows:
    \begin{align*}
      &\Let{x} 42 \In            & &\LetB 42 \In                       \\
      &\ \ \Let{y} x + 6 \In     & &\ \ \LetB \DeBruijn{0} + 6 \In     \\
      &\ \ \ \ \Let{z} y + 7 \In & &\ \ \ \ \LetB \DeBruijn{0} + 7 \In \\
      &\ \ \ \ \ \ x             & &\ \ \ \ \ \ \DeBruijn{2}
    \end{align*}

    This makes $\alpha$-equivalence of expressions trivial and avoids variable capture,
    but there are still opportunities for mistakes during transformations.
    Inserting or removing a binding requires us to traverse the binding's body
    and increase or decrease the indices of all its free variables.
    We can see this in our example when removing the innermost (unused) let-binding.
    If we naively leave the variable $\DeBruijn{2}$ untouched,
    it will not refer to the declaration $42$ anymore,
    but become a free variable:
    \begin{align*}
      &\LetB 42 \In                   \\
      &\ \ \LetB \DeBruijn{0} + 6 \In \\
      &\ \ \ \ \DeBruijn{2}\ \ \ \textit{-- incorrect, should be 1}
    \end{align*}
  }

  \Outline{intrinsically typed representation}

  \Outline{challenges of intrinsically typed representation}
  \Copied{
    In return for the guarantees provided, some additional work is required.
    For the \emph{transformation} of the intrinsically typed program,
    the programmer then has to convince the type checker
    that type- and scope-correctness invariants are preserved,
    which can be cumbersome.
  }

  \Outline{other key ideas?}

  \paragraph{Contributions}
  \TODO{contributions}

\newpage
\section{Intrinsically Typed Dead Binding Elimination}
  \Outline{briefly define de Bruijn syntax tree}
  \TODO{how much explanation? also, add reference?}
  \Copied{
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
    \end{code}

    Note that the values not only consist of natural numbers and Booleans,
    but also functions between values,
    introduced by $\lambda$-abstraction.
    Sorts can further be interpreted as Agda types,
    which we use to represent values, for example during evaluation.
  }

  \Copied{
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
  }

  \Copied{
    By indexing expressions with their type and context,
    the invariants can guarantee type- and scope-correctness by construction.
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
  }

  \Outline{thinnings encode liveness}
  \Copied{
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

    \emph{Thinnings}, also called \emph{order-preserving embeddings} (OPE)
    \cite{Chapman2009TypeCheckingNormalisation},
    support both of these interpretations:
    A thinning |Delta C= Gamma| can be used to represent the live variables |Delta|
    together with an embedding into the context |Gamma|.
    At the same time, looking at how it is constructed
    reveals for each element of the context whether it is live (|os|) or dead (|o'|).

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
  }
  \TODO{mention |..|}

  \Outline{describe transformation}
    To make the decision whether bindings can be removed,
    DBE requires liveness information of the subexpressions involved.
    Furthermore, \emph{the context} of the resulting expression
    depends on the input's variable liveness.
    Therefore, we interleave the bottom-up calculation of variable liveness
    with the transformation itself.
    The return type of the transformation could therefore be given using an existential
    list of live variables |Delta|:
    \begin{code}
      dbe : Expr sigma Gamma -> (Exists (Delta) (List I)) (Delta C= Gamma >< Expr sigma Delta)
    \end{code}
    \TODO{clarify why the result needs to be in a smaller context}

    However, it is more convenient to hide this existential using an abstraction.
    \begin{code}
      dbe : Expr sigma Gamma -> Expr sigma ^^ Gamma
    \end{code}
    \begin{code}
      record _^^_ (T : List I -> Set) (Gamma : List I) : Set where
        constructor _^_
        field
          {Delta} : List I
          thing : T Delta
          thinning : Delta C= Gamma
    \end{code}

    \paragraph{Atoms}
    Values use an empty list of variables,
    which trivially can be embedded into any context using |oe : [] C= Gamma|.
    For variables, which have one live variable,
    one can obtain a suitable thinning using the fact that
    thinnings from a singleton context are isomorphic to de Bruijn indices.
    %\begin{code}
    %  o-Ref : Ref sigma Gamma -> (sigma :: []) C= Gamma
    %  o-Ref Top      = os oe
    %  o-Ref (Pop x)  = o' (o-Ref x)
    %\end{code}
    %\begin{code}
    %  Ref-o : (sigma :: []) C= Gamma -> Ref sigma Gamma
    %  Ref-o (o' theta)  = Pop (Ref-o theta)
    %  Ref-o (os theta)  = Top
    %\end{code}

    \paragraph{Binary Operators}
    For binary operators, variables are live if they are live in one of the subexpressions
    with liveness |theta1 : Delta1 C= Gamma| and |theta2 : Delta2 C= Gamma|,
    i.e. some thinning is |os _|.
    We denote this list of live variables as |\/-vars theta1 theta2|.
    The liveness is then described by the following thinning:
    \begin{code}
      _\/_ : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= Gamma) -> \/-vars theta1 theta2 C= Gamma
      o' theta1  \/ o' theta2  = o'  (theta1 \/ theta2)
      o' theta1  \/ os theta2  = os  (theta1 \/ theta2)
      os theta1  \/ o' theta2  = os  (theta1 \/ theta2)
      os theta1  \/ os theta2  = os  (theta1 \/ theta2)
      oz         \/ oz         = oz
    \end{code}
    Furthermore, there are two thinnings \emph{into} the combined live variables,
    which allow to reconstruct the original subexpressions' thinnings,
    e.g. |un-\/1 : Delta1 C= \/-vars theta1 theta2| with
    |un-\/1 theta1 theta2 .. (theta1 \/ theta2) == theta1|.

    Since the constructors of |Expr| require the subexpressions' context to match their own,
    we need to rename the subexpressions accordingly.
    \begin{code}
      rename-Ref   : Delta C= Gamma -> Ref sigma Delta   -> Ref sigma Gamma
      rename-Expr  : Delta C= Gamma -> Expr sigma Delta  -> Expr sigma Gamma
    \end{code}

    \Outline{important detail: inefficient! (will be fixed by annotations)}
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

    \paragraph{Binders}
    When moving up over a binder, the bound variable gets removed from the context.
    In case it was part of the live variables, it also has to be removed there.
    This is done using
    |pop : (theta : Delta C= (sigma :: Gamma)) -> pop-vars theta C= Gamma|,
    again with thinnings from and into the resulting context.
    %\begin{code}
    %  pop-vars : Delta C= Gamma -> List I
    %  pop-vars {Delta = Delta}       (o' theta)  = Delta
    %  pop-vars {Delta = _ :: Delta}  (os theta)  = Delta
    %  pop-vars                       oz          = []

    %  pop : (theta : Delta C= (sigma :: Gamma)) -> pop-vars theta C= Gamma
    %  pop (o' theta)  = theta
    %  pop (os theta)  = theta
    %\end{code}
    %\begin{code}
    %  un-pop : (theta : Delta C= (sigma :: Gamma)) -> Delta C= (sigma :: pop-vars theta)

    %  law-pop-inv : (theta : Delta C= (sigma :: Gamma)) -> un-pop theta .. os (pop theta) == theta
    %\end{code}

    \paragraph{Let-bindings}
    For let-bindings, one option is to treat them as an immediate application
    of a $\lambda$-abstraction, combining the methods we just saw.
    This corresponds to weakly live variable analysis,
    since even if the variable is dead, we end up considering other variables to be live
    if they are used in its declaration.
    %\begin{code}
    %  _\l/_ : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> \/-vars theta1 (pop theta2) C= Gamma
    %  theta1 \l/ theta2 = theta1 \/ pop theta2
    %\end{code}
    The other option is to do strongly live variable analysis
    with a custom operation |_\l/_|
    that only considers variables occurrences inside the declaration if the let-binding itself is used in the body.
    %\begin{code}
    %  \l/-vars : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> Ctx
    %  \l/-vars {Delta2 = Delta2}  theta1 (o' theta2)  = Delta2
    %  \l/-vars                    theta1 (os theta2)  = \/-vars theta1 theta2
    %\end{code}
    \begin{code}
      _\l/_ : (theta1 : Delta1 C= Gamma) (theta2 : Delta2 C= (sigma :: Gamma)) -> \l/-vars theta1 theta2 C= Gamma
      theta1 \l/ (o' theta2)  = theta2
      theta1 \l/ (os theta2)  = theta1 \/ theta2
    \end{code}

    For |Let|, we split on the binding being live or dead in |dbe e2|.
    Only if it is dead will the typechecker allow us to return |e2'|
    without the binding.
    Finally, note that checking liveness \emph{after} already removing dead bindings
    from the body corresponds to \emph{strongly} live variable analysis.

  \TODO{split up cases and put next to each description? or turn whole thing into figure?}
  \Copied{
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
  }

\section{Liveness Annotations}
  \Copied{
    In compilers, it is a common pattern to perform
    separate analysis and transformation passes,
    for example with strictness and occurrence analysis in GHC
    \cite{Jones1998TransformationOptimiser}.
    We can do the same to make variable liveness information available
    without repeatedly having to compute it on the fly.
    For dead binding elimination,
    this allows us to avoid the redundant renaming of subexpressions.
  }

  \Outline{define annotated syntax}
  \Copied{
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
  }

  \Outline{describe analysis}
  \TODO{less detail}
  \Copied{
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
  }

  \Outline{describe transformation}
  \Copied{
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
  }

  \Outline{alternative: keeping annotations in result}
  \Copied{
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
  }

\section{Co-de-Bruijn Representation}
  \Copied{
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
  }

  \Outline{give intuition}
  \Copied{
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
  }

  \Outline{briefly introduce constructions}
  \TODO{much less detail}
  \Copied{
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
  }

  \Outline{define co-de-Bruijn syntax tree}
  \Copied{
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
  }

  \Outline{describe transformation}
  \Copied{
    Let-bindings make use of both a relevant pair and binding,
    without us having to think much about what the thinnings involved should look like.
    Since the context of the declaration is considered relevant
    irrespective of the let-binding itself being live,
    it corresponds to the \emph{weakly} live variables.
    Achieving \emph{strong} variable liveness would require a custom combinator,
    but more importantly, we will show that it is not necessary
    for an efficient implementation of the strong version of dead binding elimination.
    \TODO{introduce constructs? hint at conversion?}

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
  }

\section{Other Transformations}
\Outline{list others with short discussion}
\Outline{explain challenges with let-sinking}

\section{Discussion}

\subsection{Related work}
There are numerous approaches to variable binding. The POPLMark
challenge \cite{Aydemir2005POPLMark} set out to weigh the strengths
and weaknesses of different alternatives. In our current work, we did
not set out to compare different approaches to binding -- but rather
focussed on how to define transformations on the intrinsically typed
approach. In general, we expect that for simply typed approaches, such
as de Bruijn indices~\cite{DeBruijn1972NamelessIndices} or named
variables, these transformations are more straightforward to write,
but also notoriously difficult to get right.

The intrinsically typed approach to language syntax is certainly not
new. Enforcing the static type safety using indexed families dates
back at least as far as
\cite{Augustsson1999WellTypedInterpreter}. There are numerous
languages and interpreters that have been defined in this style,
including the simply typed lambda calculus~\cite{McBride2005Epigram},
mutable state~\cite{Swierstra2009Functional}, imperative programming
languages \cite{BachPoulsen2017Definitional}, probablistic programming
\cite{Saito2023Probablistic}, and many others. Many, if not all, of
these languages can be described in the more general framework
proposed by by Allais et al. \cite{Allais2018UniverseOfSyntaxes}.

Other work on verifying optimizations, such as that by
\cite{Barrack2022Intrinsically}, often focuses on those
transformations that do not change the type or context, such as
constant folding. A welcome exception is the work by Jander proving
the correctness of closure conversion~\cite{Jander2019Verifying}.  More recently,
\cite{DeMuijnckHughes2023TypeTheory} has shown how to write more
complex optimizations, including subexpression elimination, using
co-de-Bruijn variable binding.

\subsection{Further work}

The dead binding elimination may remove, but not reorder binders. This
is captured precisely by our use of thinnings. More generally,
however, transformations that permute the order of bindings cannot be
described directly in this fashion. Handling these would require a
more general notion of reordering than the thinnings used in this
work.

The language of study has been carefully chosen to be interesting yet
non-trivial. We have avoided many more advanced patterns of binding,
including recursive bindings and (mutually recursive) binding
groups. It should be possible to tackle transformations on languages
using these binders -- although we expect that doing so would
introduce a significant technical overhead.



\bibliographystyle{ACM-Reference-Format}
\bibliography{../correct-optimisations}{}

% \appendix

\end{document}
