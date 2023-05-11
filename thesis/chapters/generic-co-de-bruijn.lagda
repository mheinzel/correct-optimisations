%include agda.fmt
%include custom.fmt

\chapter{Syntax-generic co-de-Bruijn Representation}
\label{ch:generic-co-de-bruijn}
\Outline{Just a short explanation of the general idea.}
\cite{Allais2018UniverseOfSyntaxes}

\section{Descriptions of Syntax}
\label{sec:generic-co-de-bruijn-descriptions}
\Outline{Taken from \texttt{generic-syntax}, mention issues with sized types!}
\Draft{
  \paragraph{An example language}
  Using the syntax-generic approach,
  we give a description of a language equivalent to the one we used so far.
  \Fixme{describe issues with getting package to compile, especially sized types}
  \begin{code}
    data `Lang : Set where
      `App  : U -> U -> `Lang
      `Lam  : U -> U -> `Lang
      `Let  : U -> U -> `Lang
      `Val  : U -> `Lang
      `Plus : `Lang
  \end{code}
  \begin{code}
    Lang : Desc U
    Lang = \'sigma `Lang lambda where
      (`App sigma tau)  -> \'X [] (sigma => tau) (\'X [] sigma (\'# tau))
      (`Lam sigma tau)  -> \'X (sigma :: []) tau (\'# (sigma => tau))
      (`Let sigma tau)  -> \'X [] sigma (\'X (sigma :: []) tau (\'# tau))
      (`Val tau)        -> \'sigma (interpretU(tau)) lambda _ -> \'# tau
      `Plus             -> \'X [] NAT (\'X [] NAT (\'# NAT))
  \end{code}
}

\section{Terms}
\label{sec:generic-co-de-bruijn-terms}
\Draft{
  The \texttt{generic-syntax} package only interprets syntax descriptions into de Bruijn terms.
  McBride shows an interpretation into co-de-Bruijn terms
  \cite{McBride2018EveryBodysGotToBeSomewhere},
  but it is based on a different structure for syntax descriptions.
  Since we want to interpret a single description into both types of terms,
  we create our own co-de-Bruijn interpretation based on the de Bruijn version.
  \begin{code}
    interpretC_ : Desc I -> (List I -> I -Scoped) -> I -Scoped
    (interpretC(\'sigma A d))    X i Gamma  = (Exists(a)(A)) ((interpretC(d a)) X i Gamma)
    (interpretC(\'X Delta j d))  X i        = X Gamma j ><R (interpretC(d)) X i
    (interpretC(\'# j))          X i Gamma  = i == j >< Gamma == []
  \end{code}
  \begin{code}
    Scope : I -Scoped -> List I -> I -Scoped
    Scope T []                   i = T i
    Scope T (At(Delta)(_ :: _))  i = Delta |- T i
  \end{code}
  \begin{code}
    data Tm (d : Desc I) : I -Scoped where
      `var  : Tm d i (i :: [])
      `con  : (Forall (interpretC(d) (Scope (Tm d)) i => Tm d i))
  \end{code}
  The differences are that
  \begin{itemize}
    \item we use relevant pairs (|_><R_|) instead of products
    \item at the leaves (|\'#|), we constrain the context to be empty
    \item a (non-empty) scope is not just a change in context,
      but comes with an explicit wrapper (|_||-_|)
    \item variables live in a singleton context and therefore do not need an index into the context
  \end{itemize}
  This has some consequences when working with co-de-Bruijn terms,
  as ``products'' now come with thinnings and covers.
  At the end they are terminated by |\'#|, which means that even constructing a unary product
  |(interpretC(\'X Delta i (\'# j)))| requires trivial thinnings and covers, which be abstract over:
  \begin{code}
    ><R-trivial : {T : List I -> Set} → T Gamma → (T ><R lambda Gamma' -> tau == tau >< Gamma' == []) Gamma
    ><R-trivial t = pairR (t ^ oi) ((refl , refl) ^ oe) cover-oi-oe
  \end{code}
  Similarly, when deconstructing a term, we get additional thinnings
  and first need to make the fact obvious that they must be the identity and empty thinning.
  \paragraph{An example language}
  We obtain terms by interpreting our syntax description we gave before.
  \begin{code}
    Expr : U -Scoped
    Expr = Tm Lang
  \end{code}
  The evaluation function can be written in a similar way as in the concrete setting.
  It is just slightly more verbose.
  We also convince ourselves that the generic representation of this language
  indeed corresponds to the concrete one.
  We can convert between the two using structural recursion,
  the only slight pain point are the trivial relevant pairs (described above).
}
\OpenEnd{
  Generic Semantics:
  It is not sufficient to slightly tweak the de Bruijn implementation of this,
  as it relies on |interpretC_| giving rise to traversable functors, which is not true here.
  It would be very nice to get this to work, but my initial attempts didn't get far.
  Not sure it's impossible, either.
}

\section{Conversion From/To de Bruijn}
\label{sec:generic-co-de-bruijn-conversion}
\Draft{
  \paragraph{Relax}
  This is similar to the concrete implementation.
  Straightforward traversal, composing thinnings as we go.
  \begin{code}
    relax :
      (d : Desc I) -> Gamma' C= Gamma ->
      CoDeBruijn.Tm d tau Gamma' ->
      DeBruijn.Tm d tau Gamma
  \end{code}
}
\Draft{
  \paragraph{Tighten}
  This is more involved than the other direction,
  but we have already seen the crucial points in the concrete implementation.
  Relevant contexts, as well as their thinnings and covers,
  need to be discovered using |_,R_| and |_\\R_|.
  \begin{code}
  tighten :
    (d : Desc I) ->
    DeBruijn.Tm d tau Gamma ->
    CoDeBruijn.Tm d tau ^^ Gamma
  \end{code}
  Proving correctness would require some definition of semantics (e.g. evaluation).
}

\section{Dead Binding Elimination}
\label{sec:generic-co-de-bruijn-dbe}
\Outline{Note that we cannot simply remove any unused |Scope|, as we have to adhere to the (opaque) description.}
\Draft{
  We do this generically for any language with let-bindings.
  \OpenEnd{Using this for you own description. How to instantiate?}
  \OpenEnd{What about not moving into a lambda? Currently we do!
  But we would want to move into other let-bindings,
  so how can a user specify where to push and where not?}
  \begin{code}
    Let : Desc I
    Let {I} = \'sigma (I >< I) $ uncurry $ lambda sigma tau ->
      \'X [] sigma (\'X (sigma :: []) tau (\'# tau))
  \end{code}
  \begin{code}
    _\'+_ : Desc I -> Desc I -> Desc I
    d \'+ e = \'sigma Bool lambda isLeft →
                if isLeft then d else e
  \end{code}
  \begin{code}
    pattern injˡ t = true , t
    pattern injʳ t = false , t
  \end{code}
  \Fixme{these general constructs might fit better into the generic syntax background section}
  The implementation is similar to the concrete version,
  but we split it into three mutually recursive functions,
  each handling a different ``layer'' of the term datatype.
  \begin{code}
    dbe :
      Tm (d \'+ Let) sigma Gamma ->
      Tm (d \'+ Let) sigma ^^ Gamma
    dbe-⟦∙⟧ :
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
}

\section{Strong Dead Binding Elimination}
\label{sec:generic-co-de-bruijn-dbe-strong}
\Draft{
  The type signatures are identical, the implementation only differs in one place:
  Instead of checking for unused bindings before doing recursive calls,
  we do it afterwards.
  \begin{code}
    let-? : Tm (d \'+ Let) sigma ^^ Gamma -> ((sigma :: []) ⊢ Tm (d \'+ Let) tau) ^^ Gamma → Tm (d \'+ Let) tau ^^ Gamma
    let-? (t1 ^ theta1) ((oz o' \\ t2) ^ theta2) = t2 ^ theta2  -- Binding dead, just keep body.
    let-? (t1 ^ theta1) ((oz os \\ t2) ^ theta2) =              -- Assemble constructor.
      let t' ^ theta' = (t1 ^ theta1) ,R (><R-trivial (oz os \\ t2) ^ theta2)
      in `con (injʳ (_ , t')) ^ theta'
  \end{code}
  \begin{code}
    dbe (`con (injʳ (a , pairR (t1 ^ theta1) (pairR ((psi \\ t2) ^ _) ((refl , refl) ^ _) c ^ theta2) _)))
      with refl <- cover-oi-oe⁻¹ c =
        let-? (thin^^ theta1 (dbe t1)) (thin^^ theta2 (map^^ (map|- psi) (_ \\R dbe t2)))
  \end{code}
  \Fixme{Who's gonna try parsing this? Probably too much detail.}
}

\section{(Let-sinking)}
    \OpenEnd{Not implemented. Is there something interesting to say about it?}
    \Fixme{Does this belong in Further Work instead?}
