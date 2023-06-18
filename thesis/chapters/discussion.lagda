%include agda.fmt
%include custom.fmt

\chapter{Discussion}
\label{ch:discussion}
  \paragraph{Summary}
    As demonstrated in this thesis,
    binding-related program transformations
    can be performed on intrinsically typed syntax trees.
    To avoid redundant traversals,
    it is beneficial to compute variable liveness information upfront,
    e.g. providing it as part of the syntax tree.

    Thinnings proved to be useful for
    reasoning about variable liveness of expressions
    and, in simple cases, manipulating their context.
    This is also witnessed by the connection
    between weakly live variable analysis and the co-de-Bruijn representation,
    which is built around thinnings.

    Finally, it seems promising to define binding-related transformations
    syntax-generically,
    as they often handle most language language constructs in a uniform way.
    This was showcased by
    performing dead binding elimination generically on co-de-Bruijn expressions
    of any language containing let-bindings.

  \paragraph{Reordering bindings}
    While thinnings worked well for dead binding elimination,
    the let-sinking transformation suffered from their order-preserving nature,
    requiring another mechanism to describe the reordering of bindings.

    One could attempt to address this issue by extending thinnings
    to allow for permutations,
    but this might just move the complexity,
    as the operations on thinnings then become more difficult to define.
    For example, it is not obvious how to perform the liveness union operation |_\/_|
    without a way of ensuring that the reorderings in both its arguments agree
    with each other.

    Another approach that is also used by Allais et~al. is to define thinnings
    as a function
    |(forall sigma -> Ref sigma Delta -> Ref sigma Gamma)|
    on references.
    This has some advantages, as it naturally supports reordering
    and inherits associativity and identity laws by virtue of being a function.
    However, the representation as a function is opaque
    and not even guaranteed to be injective
    (so the source context could be larger than the target context).
    This makes it difficult to talk about equality
    and define operations on thinnings.


\section{Further Work}
\label{sec:further-work}
    In addition to the challenges around reordering bindings,
    there are several other open ends that we could not address due to lack of time.
    For example, attempting a proof of correctness for the
    de Bruijn version of let-sinking might be simpler
    than for the co-de-Bruijn variant we failed to complete
    in section \ref{sec:co-de-bruijn-let-sinking}.
    However, it might be wiser to first improve the implementation
    (regarding reordering bindings)
    before trying to prove it correct.

    The syntax-generic co-de-Bruijn approach
    could also benefit from further exploration.
    As noted in section \ref{sec:generic-co-de-bruijn-discussion},
    syntax-generic let-sinking comes with some interesting questions.
    Another large topic we only discussed briefly is that of correctness
    which first requires a suitable notion of semantics.
    The most promising avenue for that is to extend the work by Allais et~al.
    \cite{Allais2018UniverseOfSyntaxes}
    not just with basic support for co-de-Bruijn terms,
    but also for notions such as |Semantics|.

    There are several techniques that are related to aspects of the work shown here.
    For example, we saw several distinct definitions of syntax trees
    with a different amount of extra information on them:
    raw expressions,
    intrinsically typed expressions with some invariants,
    and annotated expressions that also contain the results of some program analysis.
    However, the language they describe is fundamentally the same.
    Making this relationship explicit using \emph{ornamentations}
    \cite{Dagand2014TransportingFunctionsAcrossOrnaments}
    could replace ad-hoc definitions like |forget|.
    Similarly, many program analyses can be studied through
    the common framework of \emph{coeffects} \cite{Petricek2014Coeffects}.

    Finally, the existing work can be extended with additional
    language constructs and transformations, each posing new challenges.


\subsection{Extending the Language}
  \paragraph{Recursive bindings}
    In a recursive let-binding, the bound variable is available in its own declaration.
    While this only requires a small change in the definition of the syntax tree,
    evaluation can now diverge.
    The treatment of semantics requires significant changes to account for this partiality
    \cite{%
      Bove2014PartialityRecursion,%
      Capretta2005GeneralRecursion,%
      McBride2015TuringCompletenessTotallyFree,%
      Danielsson2012PartialityMonad%
    }
    Program analysis of recursive functions poses additional challenges
    \cite{Nielson1999PrinciplesProgramAnalysis}
    and transformations are affected as well:
    In the presence of effects such as non-termination,
    removing or reordering let-bindings is only semantics-preserving
    if their declarations can be shown to be pure (i.e. terminating).

  \paragraph{Mutually recursive binding groups}
    Since mutual recursion allows multiple bindings to refer to each other,
    the current approach of handling one binding at a time is not sufficient.
    Instead, there is a list of simultaneous declarations
    where the scope of each is extended with a all of the bindings.
    This can be represented in the syntax tree without too much effort,
    even using the generic syntax descriptions seen before.
    \Fixme{I have code to show it, but doesn't make sense to show it here.}
    % \begin{code}
    %   RecBindings : List I -> I -> Desc I
    %   RecBindings Delta tau = foldr (\'X Delta) (\'X Delta tau (\'# tau)) Delta
    % \end{code}
    Manipulating this structure,
    e.g. splitting binding groups into strongly connected components,
    is expected to be challenging, but potentially instructive.


\subsection{Other Transformations}
  \paragraph{Local rewrites}
    There is a number of local transformations
    that simply rewrite a specific pattern into an equivalent one.
    Most examples can always be performed safely:
    \begin{itemize}
      \item constant folding and identities, \\
        e.g. $P + 0 \ \Rightarrow \ P$
      \item turning beta redexes into let-bindings, \\
        i.e. $(\lambda x.\ Q)\ P \ \Rightarrow \ \Let{x} P \In Q$
      \item floating let-bindings out of function application, \\
        i.e. $(\Let{x} P \In Q)\ R \ \Rightarrow \ \Let{x} P \In Q\ R$
    \end{itemize}
    A general fold-like function should allow
    to specify a single instance of a rewrite
    and then apply it wherever possible
    in a pass over the whole program.
    Similarly, the overall preservation of semantics
    should follow from that of a single rewrite instance.

  % \paragraph{Let-floating}
  %   Peyton Jones et al. not only discuss let-sinking,
  %   but also floating let-bindings out of lambdas,
  %   which they also refer to as \emph{full laziness} transformation
  %   \cite{Jones1996LetFloating}.

  \paragraph{Common subexpression elimination}
    The aim of this transformation is to find subexpressions that occur multiple times
    and replace them with a variable refering to a single matching declaration,
    reducing both code size and work performed during evaluation.
    % A basic implementation keeps track of the declaration of all bindings in scope
    % to find any occurrences of the same expression.
    For a basic implementation it suffices to try finding occurrences of expressions
    that are the same as the declaration of a binding already in scope.
    A more powerful approach is to put more work into identifying common subexpressions
    and making the transformation itself introduce shared bindings
    at suitable points.

    In de Bruijn representation,
    identifying identical subexpressions is challenging,
    since their context (and thus their type) may be different.
    This problem is avoided by co-de-Bruijn representation.
