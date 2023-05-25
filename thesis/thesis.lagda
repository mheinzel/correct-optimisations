\documentclass{report}

% workaround, see https://github.com/kosmikus/lhs2tex/issues/82
\let\Bbbk\undefined

%include agda.fmt
%include custom.fmt



\include{preamble}

\begin{document}

\include{title}

\abstract

Variable representations used in compilers
usually rely on the compiler writers' diligence to maintain complex invariants.
Program transformations that manipulate the binding structure are therefore tricky to get right.
In a dependently typed programming language such as Agda,
we can however make use of intrinsically typed syntax trees
to enforce type- and scope-safety by construction,
ruling out a large class of binding-related bugs.
We show how to perform (and prove correct) dead binding elimination and let-sinking using intrinsically typed de Bruijn indices.
To avoid repeated traversals of the transformed expression,
we include variable liveness information into the syntax tree and later employ a co-de-Bruijn representation.
Finally, we perform transformations in this style syntax-generically.


\tableofcontents


\include{chapters/introduction}

\include{chapters/preliminaries}

\include{chapters/de-bruijn}

\include{chapters/co-de-bruijn}

\include{chapters/generic-co-de-bruijn}

\chapter{Discussion}
\section{Related Work}
\section{Further Work}


\bibliography{../correct-optimisations}{}


\appendix

\includepdf[pages=1,offset=0cm -2.5cm,scale=0.55,pagecommand=\chapter{Ethics Quick Scan}\label{app:ethics-quick-scan}]{ethics-privacy-quick-scan-results-anonymised.pdf}
\includepdf[pages=2-,scale=0.55,pagecommand=\thispagestyle{plain}]{ethics-privacy-quick-scan-results-anonymised.pdf}

\end{document}
