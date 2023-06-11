%include agda.fmt
%include custom.fmt

\chapter{Syntax-generic Co-de-Bruijn Representation}
\label{ch:generic-co-de-bruijn}
    So far, we worked with specialised types for the syntax trees
    of the language we defined.
    Modifying the language or defining a new one
    would require us to also modify the implementations
    of each transformation.
    However, the core of the transformation would likely remain unchanged:
    dead binding elimination for example only needs to know
    where variables are bound and occur in the expression,
    and then exclusively modifies let-bindings.
    All other parts of the syntax tree simply get traversed in a highly uniform way.

    This problem is addressed by Allais et al.
    \cite{Allais2018UniverseOfSyntaxes}
    with the concept of syntax-generic programming,
    although based on a de Bruijn representation.
    The main idea is to:
    \begin{enumerate}
      \item define a datatype of syntax descriptions |Desc|
      \item describe a family of terms |Tm d sigma Gamma| for each |(d : Desc I)|
      \item implement operations \emph{once}, generically over descriptions
      \item describe your language using |Desc| to get access to all generic operations
    \end{enumerate}

    To define the syntax-generic co-de-Bruijn terms,
    we build on top of the \texttt{generic-syntax}
    \footnote{\url{https://github.com/gallais/generic-syntax}}
    Agda package,
    which is an artefact of the abovementioned paper.
    It failed to compile with recent versions of Agda,
    mainly due to issues with sized types, which were used to show termination.
    Therefore, we trimmed the package down to the parts interesting to us
    and removed the size information from all types.
    The paper still serves as a great introduction to the topic,
    but we will start with a short overview of the main
    constructions we use.


\section{Descriptions of Syntax}
\label{sec:generic-co-de-bruijn-descriptions}
    At the core of this chapter is the the type of syntax descriptions,
    taken verbatim from Allais et al.
    \begin{code}
      data Desc (I : Set) : Set1 where
        \'o : (A : Set) -> (A -> Desc I) -> Desc I
        \'X : List I -> I -> Desc I -> Desc I
        \'# : I -> Desc I
    \end{code}
    |I| is the type associated with each expression and variable brought into scope,
    typically their sort.
    Variable occurrences do not need to be modeled in the description,
    are part of any language implicitly.

    The constructor |\'o| is then used to store data of some type |A|.
    Since the remaining description can then depend on the value of the data,
    it can be used as a tag deciding which constructor of the syntax tree is present.
    |\'X| can be used for recursion (i.e. subexpressions)
    with a list of variables that come into scope and specified sort.
    After building a product-like structure
    (including sums by using the dependent product |\'o|),
    the descriptions are terminated with |\'#|,
    stating their sort.

  \paragraph{Example}
    Let us give a description of our expression language
    to get a feeling for syntax descriptions.
    We start by defining a type of tags for each type of syntax node
    (except variable occurrences, as noted above).
    Each tag also carries the sorts it will use.
    \begin{code}
      data `Lang : Set where
        `App  : U -> U -> `Lang
        `Lam  : U -> U -> `Lang
        `Let  : U -> U -> `Lang
        `Val  : U -> `Lang
        `Plus : `Lang
    \end{code}
    Once we plug the type into |\'o|, we can give a description
    for each of the constructors.
    Those are typically a product of multiple subexpressions.
    While the details can be hard to follow,
    some similarities with the original |Expr| type we defined should become apparent.
    \begin{code}
      Lang : Desc U
      Lang = \'o `Lang lambda where
        (`App sigma tau)  -> \'X [] (sigma => tau) (\'X [] sigma (\'# tau))
        (`Lam sigma tau)  -> \'X [ sigma ] tau (\'# (sigma => tau))
        (`Let sigma tau)  -> \'X [] sigma (\'X [ sigma ] tau (\'# tau))
        (`Val tau)        -> \'o (interpretU(tau)) lambda _ -> \'# tau
        `Plus             -> \'X [] NAT (\'X [] NAT (\'# NAT))
    \end{code}

\section{Intrinsically Typed Syntax}
\label{sec:generic-co-de-bruijn-terms}
    The \texttt{generic-syntax} package only interprets syntax descriptions into de Bruijn terms.
    McBride shows an interpretation into co-de-Bruijn terms
    \cite{McBride2018EveryBodysGotToBeSomewhere},
    but it is based on a different structure of syntax descriptions.
    Since we want to interpret a single description type into both types of terms,
    it is not directly reusable.
    However, the building blocks for bindings and relevant pairs
    still help us to create our own co-de-Bruijn interpretation.

    We start be interpreting descriptions into flat (non-recursive)
    types representing a single syntax node,
    where the argument |X| marks the recursive occurrences
    and can later be used to form a fixpoint.
    \begin{code}
      _-Scoped : Set -> Set1
      I -Scoped = I -> List I -> Set
    \end{code}
    \begin{code}
      interpretC_ : Desc I -> (List I -> I -Scoped) -> I -Scoped
      (interpretC(\'o A d))        X i Gamma  = (Exists(a)(A)) ((interpretC(d a)) X i Gamma)
      (interpretC(\'X Delta j d))  X i        = X Delta j ><R (interpretC(d)) X i
      (interpretC(\'# j))          X i Gamma  = i == j >< Gamma == []
    \end{code}
    The interpretation of |\'o| is exactly the same as for de Bruijn terms,
    storing a value of type A and (based on its value)
    continuing with the remaining description.
    The other two cases however need to enforce the invariants on the live context |Gamma|
    by which the expressions are indexed:
    |\'X| uses \emph{relevant} pairs and |\'#| requires
    that the context starts out empty until something explicitly extends it.

    Based on that, we can build the recursive type of terms.
    At each recursive occurrence, a is introduced.
    While this could be done as |Delta ||- T i|
    independent of the bound variables |Delta|,
    a single case distinction avoids a trivial wrapper with a thinning
    |[] C= []|.
    \begin{code}
      Scope : I -Scoped -> List I -> I -Scoped
      Scope T []                   i = T i
      Scope T (At(Delta)(_ :: _))  i = Delta |- T i
    \end{code}
    \begin{code}
      data Tm (d : Desc I) : I -Scoped where
        `var  : Tm d i [ i ]
        `con  : (interpretC(d)) (Scope (Tm d)) i Gamma -> Tm d i Gamma
    \end{code}
    We also see that variables always have a singleton live context.

  \paragraph{Instantiation the terms}
    We can obtain co-de-Bruijn terms of our expression language
    using the description we created.
    \begin{code}
      Expr : U -Scoped
      Expr = Tm Lang
    \end{code}
    These are isomorphic to the co-de-Bruijn syntax tree we defined manually.
    However, there are some practical differences coming from
    the way relevant products are used in the interpretation.
    At the end, each description is terminated by a |\'#|
    resulting in an expression with empty live context,
    which means that even constructing a unary product
    |(interpretC(\'X Delta i (\'# j)))|
    requires trivial thinnings and covers.

    This is not an issue when working generically,
    but when constructing a term for a concrete description,
    it causes some boilerplate,
    even for a simple program such as $\text{foo} = f\ 1$.

    \begin{code}
      -- de Bruijn
      foo :: Expr BOOL [ NAT => BOOL ]
      foo = App (Var Top) (Val 1)

      -- co-de-Bruijn
      foo :: Expr BOOL [ NAT => BOOL ]
      foo = App (pairR (os oz ^ Var) (o' oz ^ Val 1) (cs' czz))

      -- syntax-generic co-de-Bruijn
      foo : Expr BOOL [ NAT => BOOL ]
      foo =
        `con ( `App NAT BOOL ,
          pairR
            (`var ^ os oz)
            (pairR  ((`con ((`Val NAT) , (1 , (refl , refl)))) ^ oz)
                    ((refl , refl) ^ oz)
                    czz
              ^ o' oz)
            (cs' czz))
    \end{code}

    Luckily, the boilerplate during construction of terms
    can be reduced using smart constructors (e.g. pattern synonyms |App|, |Lam|, \ldots)
    or a general helper of this shape:
    \begin{code}
      ><R-trivial : {T : List I -> Set} ->
        T Gamma -> (T ><R lambda Delta -> tau == tau >< Delta == []) Gamma
      ><R-trivial t = pairR (t ^ oi) ((refl , refl) ^ oe) cover-oi-oe
    \end{code}
    However, when deconstructing a term,
    it is not clear to the typechecker that the redundant thinnings must be
    identity and empty thinning (|oi| and |oe|) respectively,
    so we cannot just use pattern synonyms to hide them away.
    We first need to make the fact obvious in a \textbf{with}-abstraction
    calling a helper function:
    \begin{code}
      ><R-trivial-1 : {T : List I -> Set} ->
        (T ><R lambda Delta -> tau == tau' >< Delta == []) Gamma -> T Gamma >< tau == tau'
      ><R-trivial-1 (pairR (t ^ theta1) ((refl , refl) ^ theta2) cover)
        with refl ← cover-oi-oe-1 cover =
          t , refl
    \end{code}
    This affects any operation on our language
    by introducing additional \textbf{with}-abstractions.
    Evaluation or also converting into the concrete co-de-Bruijn representation,
    for example, should be absolutely trivial, but end up somewhat verbose.


\section{Conversion From/To de Bruijn Syntax}
\label{sec:generic-co-de-bruijn-conversion}
    The conversion between de Bruijn and co-de-Bruijn terms
    can be done generically for any description.
    \begin{code}
      relax : (d : Desc I) -> Delta C= Gamma ->
        CoDeBruijn.Tm d tau Delta -> DeBruijn.Tm d tau Gamma
      tighten : (d : Desc I) ->
        DeBruijn.Tm d tau Gamma -> CoDeBruijn.Tm d tau ^^ Gamma
    \end{code}
    While the operations used in the implementation are generally the same
    as in the concrete setting,
    the structure is noticeably different.
    Instead of handling each constructor of the language,
    we use three mutually recursive functions to handle scopes,
    variables and constructors, respectively.
    We will see the same approach in more detail
    when doing dead binding elimination
    in the next section.


\section{Dead Binding Elimination}
\label{sec:generic-co-de-bruijn-dbe}
    Dead binding elimination can be written in a way that abstracts
    over most of the language, but it does not quite work for any description.
    The description at least needs to feature let-bindings,
    but how can we express this requirement in the type signature?
    While it would be useful to be able to directly plug in our description type
    together with some kind of witness of how it contains let-bindings,
    this comes with some complexity.
    Since this is mainly an issue of ergonomics
    and not directly relevant to our goal of performing transformations,
    we adopt a simpler solution from Allais et al.'s paper.

  \paragraph{Type signature}
    We make use of the fact that descriptions are closed under sums.
    This allows to describe constructors of a language separately
    and then combine them.
    \begin{code}
      _\'+_ : Desc I -> Desc I -> Desc I
      d \'+ e = \'o Bool lambda isLeft ->
                  if isLeft then d else e
    \end{code}
    \begin{code}
      pattern inl t = true , t
      pattern inr t = false , t
    \end{code}
    For our use case, we describe let-bindings
    and then define dead binding elimination for any description
    explicitly extended with them.
    \begin{code}
      `Let : Desc I
      `Let {I} = \'o (I >< I) $ uncurry $ lambda sigma tau ->
        \'X [] sigma (\'X [ sigma ] tau (\'# tau))
    \end{code}
    \begin{code}
      dbe : Tm (d \'+ `Let) sigma Gamma -> Tm (d \'+ `Let) sigma ^^ Gamma
    \end{code}

    The observations made about the return type in the concrete setting still apply,
    so the result again comes with a thinning.

  \paragraph{Transformation}
    The implementation is mostly similar to the concrete version,
    but we split it into three mutually recursive functions,
    each handling a different ``layer'' of the term datatype.
    \begin{code}
      dbe :
        Tm (d \'+ `Let) sigma Gamma ->
        Tm (d \'+ `Let) sigma ^^ Gamma

      dbe-[.] :
        (d' : Desc I) ->
        (interpretC(d')) (Scope (Tm (d \'+ `Let))) tau Gamma ->
        (interpretC(d')) (Scope (Tm (d \'+ `Let))) tau ^^ Gamma

      dbe-Scope :
        (Delta : List I) ->
        Scope (Tm (d \'+ `Let)) Delta tau Gamma ->
        Scope (Tm (d \'+ `Let)) Delta tau ^^ Gamma
    \end{code}
    The last two of these functions traverse a single syntax node,
    apply |dbe| to each subexpression and combine the
    resulting live contexts using the co-de-Bruijn smart constructors.
    \begin{code}
      dbe-[.] (\'o A d) (a , t) =
        map^^ (a ,_) (dbe-[.] (d a) t)
      dbe-[.] (\'X Delta j d) (pairR (t1 ^ theta1) (t2 ^ theta2) c) =
        thin^^ theta1 (dbe-Scope Delta t1) ,R thin^^ theta2 (dbe-[.] d t2)
      dbe-[.] (\'# i) t =
        t ^ oi

      dbe-Scope [] t = dbe t
      dbe-Scope (_ :: _) (psi \\ t) = map^^ (map|- psi) (_ \\R dbe t)
    \end{code}

    The implementation of |dbe| itself is split into
    a case for variables,
    a case for the description |d|
    and finally a case for let-bindings, where most of the work happens.
    We would like to write the following:
    \begin{code}
      dbe `var = `var ^ oi
      dbe (`con (inl t)) = map^^ (`con . inl) (dbe-[.] _ t)
      dbe (`con (inr (At(t)(a , pairR (t1 ^ theta1) (p ^ theta2) _))))
        with ><R-trivial-1 p
      ...  | (o' oz \\ t2) , refl =
          thin^^ theta2 (dbe t2)
      ...  | (os oz \\ t2) , refl =
          map^^ (`con . inr) (dbe-[.] `Let t)
    \end{code}
    However, this definition fails Agda's termination checker,
    which can for example be solved by manually inlining the call to |dbe-[.] `Let|
    in the last line.

    For the strong version, we again introduce a helper function |Let?|
    and now everything works nicely:
    since it only checks for dead bindings afterwards,
    the recursive call happens directly on the subexpression from the input,
    which is clearly structurally smaller.
    \begin{code}
      Let? : (interpretC(`Let)) (Scope (Tm (d \'+ `Let))) tau Gamma -> Tm (d \'+ `Let) tau ^^ Gamma
      Let? (At(t)(a , pairR (t1 ^ theta1) (p ^ theta2) _))
        with ><R-trivial-1 p
      ... | (o' oz \\ t2) , refl = t2 ^ theta2
      ... | (os oz \\ t2) , refl = `con (inr t) ^ oi

      dbe `var            = `var ^ oi
      dbe (`con (inl t))  = map^^ (`con . inl) (dbe-[.] _ t)
      dbe (`con (inr t))  = bind^^ Let? (dbe-[.] `Let t)
    \end{code}


\section{Discussion}
    \Outline{Nice and concise. Generic.}
    \Outline{Complexity through abstractions? |><R-trivial| \ldots}
    \OpenEnd{
      What about let-sinking into a lambda?
      But we would want to move into other let-bindings,
      so how can a user specify where to push and where not?
    }
    \Outline{Correctness? Using which semantics?}
    \OpenEnd{
      Generic Semantics:
      It is not sufficient to slightly tweak the de Bruijn implementation of this,
      as it relies on |interpretC_| giving rise to traversable functors, which is not true here.
      It would be very nice to get this to work, but my initial attempts didn't get far.
      Not sure it's impossible, either.
    }
