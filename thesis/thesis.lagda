\documentclass{report}

% workaround, see https://github.com/kosmikus/lhs2tex/issues/82
\let\Bbbk\undefined

%include agda.fmt
%include custom.fmt



\include{preamble}

\begin{document}

\include{title}

\abstract

\tableofcontents


\include{chapters/introduction}

\include{chapters/program-transformations}

\include{chapters/binding-representation}

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
