\documentclass{article}

% workaround, see https://github.com/kosmikus/lhs2tex/issues/82
\let\Bbbk\undefined

%include agda.fmt
%include custom.fmt

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{stmaryrd}
\usepackage{listings}
\usepackage{xcolor}
\usepackage{xspace}
\usepackage{natbib}
\usepackage{hyperref}
\usepackage{todonotes}

% \newcommand{\Draft}[1]{}
\newcommand{\Draft}[1]{\todo[inline,backgroundcolor=gray!30]{#1}}

\citestyle{acmauthoryear}

\title{Thesis Proposal: Analysis and Transformation of Intrinsically Typed Syntax}

\author{Matthias Heinzel}

\date{\today}

\begin{document}

\maketitle

\tableofcontents
\pagebreak

\section{Introduction}
\Draft{What is the problem? Illustrate with an example.}
\Draft{What is/are your research questions/contributions?}

\section{Background}
\Draft{What is the existing technology and literature that I'll be studying/using in my research?}
\subsection{Program Analysis and Transformation}
\subsection{Intrinsically Typed Syntax}
\subsection{Datatype-generic Programming}
% Immediately go into the syntax-related work, just a short overview, link to literature
% (might not end up being in the thesis)

\section{Preliminary Results}
\Draft{What examples can you handle already?}
\Draft{What prototype have I built?}
\Draft{How can I generalize these results? What problems have I identified or do I expect?}
\subsection{Dead Binding Elimination}
\subsection{Observations}

\section{Timetable and Planning}
\subsection{Further Work}
\Draft{What will I do with the remainder of my thesis?}
\subsection{Schedule}
\Draft{Give an approximate estimation/timetable for what you will do and when you will be done.}


\bibliographystyle{ACM-Reference-Format}
\bibliography{../correct-optimisations}{}

\end{document}
