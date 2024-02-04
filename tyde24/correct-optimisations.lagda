\documentclass[sigplan,screen]{acmart}

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

\acmConference[TyDe ’24]{Workshop on Type-Driven Development}{September 2, 2024}{Milan, Italy}

\begin{document}

% TODO
\title{Provingly Correct Optimisations on Intrinsically Typed Expressions}

\author{Matthias Heinzel}
\affiliation{%
  \institution{Well-Typed LLP}
  % \city{London}
  \country{United Kingdom}}
\email{matthias@@well-typed.com}

\begin{abstract}
  \Outline{abstract}
\end{abstract}

\keywords{Intrinsically Typed Syntax, Dependent Types, Agda}

\maketitle

\section{Introduction}
\Outline{describe problem, can we do transformations correctly?}
\Outline{describe transformations}
\Outline{contributions/structure}

\section{Dead Binding Elimination}
\Outline{de Bruin}
\Outline{tracking liveness}
\Outline{co-de-Bruin}
% TODO: how do correctness proofs fit in? check what I have.

\section{Other Transformations}
\Outline{list others with short discussion}
\Outline{explain challenges with let-sinking}

\section{Related Work}

\section{Conclusion}
\Outline{or Discussion?}

\bibliographystyle{ACM-Reference-Format}
\bibliography{../correct-optimisations}{}

% \appendix

\end{document}
