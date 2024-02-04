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
TODO
\end{abstract}

\keywords{Intrinsically Typed Syntax, Dependent Types, Agda}

\maketitle

\section{Introduction}

TODO

\bibliographystyle{ACM-Reference-Format}
\bibliography{../correct-optimisations}{}

% \appendix

\end{document}
