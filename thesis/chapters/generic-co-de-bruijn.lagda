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
  \Draft{Note that we cannot simply remove any unused |Scope|, as we have to adhere to the (opaque) description.}
  \Draft{
    We do this generically for any language with let-bindings.
    \OpenEnd{Using this for you own description. How to instantiate?}
    \OpenEnd{What about not moving into a lambda? Currently we do!
    But we would want to move into other let-bindings,
    so how can a user specify where to push and where not?}
    \begin{code}
      Let : Desc I
      Let {I} = \'o (I >< I) $ uncurry $ lambda sigma tau ->
        \'X [] sigma (\'X [ sigma ] tau (\'# tau))
    \end{code}
    \begin{code}
      _\'+_ : Desc I -> Desc I -> Desc I
      d \'+ e = \'o Bool lambda isLeft ->
                  if isLeft then d else e
    \end{code}
    \begin{code}
      pattern inl t = true , t
      pattern inr t = false , t
    \end{code}
    The implementation is similar to the concrete version,
    but we split it into three mutually recursive functions,
    each handling a different ``layer'' of the term datatype.
    \begin{code}
      dbe :
        Tm (d \'+ Let) sigma Gamma ->
        Tm (d \'+ Let) sigma ^^ Gamma
      dbe-[.] :
        (interpretC(d)) (Scope (Tm (d' \'+ Let))) tau Gamma ->
        (interpretC(d)) (Scope (Tm (d' \'+ Let))) tau ^^ Gamma
      dbe-Scope :
        (Delta : List I) ->
        Scope (Tm (d \'+ Let)) Delta tau Gamma ->
        Scope (Tm (d \'+ Let)) Delta tau ^^ Gamma
    \end{code}
    The implementation of |dbe| is split into
    a case for constructors of the unknown description |d|
    and a case for let-bindings, where most of the work happens.

    For strong version: Instead of checking for unused bindings before doing recursive calls,
    we do it afterwards.
    \begin{code}
      Let? : Tm (d \'+ Let) sigma ^^ Gamma -> ([ sigma ] |- Tm (d \'+ Let) tau) ^^ Gamma -> Tm (d \'+ Let) tau ^^ Gamma
      Let? (t1 ^ theta1) ((oz o' \\ t2) ^ theta2) =
        t2 ^ theta2
      Let? (t1 ^ theta1) ((oz os \\ t2) ^ theta2) =
        let t' ^ theta' = (t1 ^ theta1) ,R (><R-trivial (oz os \\ t2) ^ theta2)
        in `con (inr (_ , t')) ^ theta'
    \end{code}
    \begin{code}
      dbe (`con (inr t)) = bind^^ Let? (dbe-[.] {d = `Let} t)
    \end{code}
    \Fixme{Who's gonna try parsing this? Probably too much detail.}
  }

\section{Discussion}
    \Outline{Nice and concise. Generic.}
    \Outline{Complexity through abstractions? |><R-trivial| \ldots}
    \Outline{Correctness? Using which semantics?}
    \OpenEnd{
      Generic Semantics:
      It is not sufficient to slightly tweak the de Bruijn implementation of this,
      as it relies on |interpretC_| giving rise to traversable functors, which is not true here.
      It would be very nice to get this to work, but my initial attempts didn't get far.
      Not sure it's impossible, either.
    }
