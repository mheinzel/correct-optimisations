\documentclass{report}

% workaround, see https://github.com/kosmikus/lhs2tex/issues/82
\let\Bbbk\undefined

%include agda.fmt
%include custom.fmt



\input{preamble}

\begin{document}

\include{title}

\abstract

\input{chapters/abstract}


\tableofcontents


\include{chapters/introduction}

\include{chapters/preliminaries}

\include{chapters/de-bruijn}

\include{chapters/co-de-bruijn}

\include{chapters/generic-co-de-bruijn}

\include{chapters/discussion}


\bibliography{../correct-optimisations}{}


\end{document}
