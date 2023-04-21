%include agda.fmt
%include custom.fmt

\chapter{co-de-Bruijn Representation}
\label{ch:co-de-bruijn}

\section{Intrinsically Typed Syntax}
\label{sec:co-de-bruijn-intrinsically-typed}
\Draft{
  We follow McBride's work on co-de-Bruijn representation
  \cite{McBride2018EveryBodysGotToBeSomewhere}
  and use OPEs |_C=_| to define the type of relevant pairs |_><R_|
  where each variable in the context must be in the context of one of the two subexpressions,
  as well as bound variables |_||-_|.
  \begin{code}
    data Expr : (sigma : U) (Gamma : Ctx) -> Set where
      Var : Expr sigma (sigma :: [])
      App : (Expr (sigma => tau) ><R Expr sigma) Gamma -> Expr tau Gamma
      Lam : ((sigma :: []) |- Expr tau) Gamma -> Expr (sigma => tau) Gamma
      Let : (Expr sigma ><R ((sigma :: []) |- Expr tau)) Gamma -> Expr tau Gamma
      Val : (v : (interpretU(sigma))) -> Expr sigma []
      Plus : (Expr NAT ><R Expr NAT) Gamma -> Expr NAT Gamma
  \end{code}
}

\section{Conversion From/To de Bruijn}
\label{sec:co-de-bruijn-conversion}
\Draft{
  \paragraph{Relax}
  The main difference here is that
  variables are not kept in the context until the latest,
  but discarded at the earliest opportunity.
  More concretely,
  in de Bruijn representation, subexpressions keep the full context of available bindings,
  while in co-de-Bruijn representation an OPE selects the subset that occurs.
  A converted expression will therefore generally be required to have a larger context than before,
  indicated by an OPE.
  \begin{code}
    from :  Gamma' C= Gamma -> Expr sigma Gamma' -> DeBruijn.Expr sigma Gamma
  \end{code}
  The implementation proceeds by induction over the syntax,
  composes OPEs on the way
  and finally at the variable makes use of the fact
  that an OPE from a singleton list is isomorphic to a de Bruijn reference.
  The proof of semantic equivalence mainly consists of congruences.
}
\Draft{
  \paragraph{Tighten}
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
    into : DeBruijn.Expr sigma Gamma -> Expr sigma ^^ Gamma
  \end{code}
}

\section{Dead Binding Elimination}
\label{sec:co-de-bruijn-dbe}
\Draft{
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
  \paragraph{Correctness}
  \OpenEnd{
  No correctness proof yet, but can probably be copied from the strong version
  (with only minimal changes).
  }
}

\section{Strong Dead Binding Elimination}
\label{sec:co-de-bruijn-dbe-strong}
\Draft{
  To avoid this,
  instead of identifying unused bound variables in the input expression,
  we can do the recursive call \emph{first} and check whether the variable is used
  \emph{afterwards}.
  \Fixme{unexplained operations, hard to follow}
  \begin{code}
    let-? : (Expr sigma ><R ((sigma :: []) |- Expr tau)) Gamma -> Expr tau ^^ Gamma
    let-?         (pairR _ ((oz o' \\ e2)  ^ theta2)  _)  = e2 ^ theta2
    let-? (At(p)  (pairR _ ((oz os \\ _)   ^ _)       _)) = Let p ^ oi
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
}

\section{Pushing let-bindings Inwards}
\label{sec:co-de-bruijn-let-floating}
\Draft{
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
  \Fixme{reword, explain why there are not two cases anymore}
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
  The context is split into four segments (where |Gamma3| is |sigma :: []|).
  Since subexpressions are in their own context,
  we first need to split their context (and the thinnings) into segments as well.
  This is also true for the cover, which then needs to be carefully reassembled.
  Going under binders requires rewriting using list concatenation's associativity.
  \paragraph{Binary constructors}
  Variable usage information is immediately available:
  We split and examine the thinnings of the subexpressions to see where the declaration is used.
  Using the cover, we can rule out the case where no subexpression uses the declaration.
  No strengthening is necessary, discovering that a variable is unused is enough.
  The subexpressions are then combined using |_,R_|, creating the new thinnings and cover for us.
  \paragraph{Binders}
  No weakening of the declaration is necessary anymore, we simply update its thinning.
  But recursing into the body of another let-binding still complicates things:
  Although we know that its variable usage should be unaffected,
  the type signature of |push-let| does not enforce that
  and we need to split its thinning.
  \paragraph{Correctness}
  \OpenEnd{
  Work on the proof is in progress, but it's messy.
  There are many lemmas about splitting OPEs, reordering the context etc.
  It seems like some of the complications could be avoided
  if we manage to avoid the usage of |_,R_| as explained in the next paragraph.
  }
  \paragraph{Covers}
  As hinted at above, it should not be necessary to return a result with a thinning.
  If all variables occur in either declaration or body, they will still occur in the result.
  This would also simplify the implementation (and thus the proof),
  since constructing a relevant pair directly is a simpler operation
  than using |_,R_| to discover a coproduct with new thinnings.
  However, constructing the required covers from the input requires non-trivial manipulation
  (splitting, composition, concatenation) and observing some equalities.
  \OpenEnd{
  Can we get this to work? It seems like the ``right'' way of doing things, but not easy.
  }
}

\section{Discussion}
\label{sec:co-de-bruijn-discussion}
\Outline{This was nice, although (...). Can we generalise this?}
