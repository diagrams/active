%% -*- LaTeX -*-

\documentclass[9pt,preprint,authoryear,nocopyrightspace]{sigplanconf}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{latexsym}
\usepackage{amssymb}
\usepackage{stmaryrd}
\usepackage{comment}
\usepackage{url}
\usepackage{xspace}
\usepackage{xcolor}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Page size

\pdfpagewidth=8.5in
\pdfpageheight=11in

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Diagrams

\usepackage{graphicx}
\usepackage[outputdir=diagrams/]{diagrams-latex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Prettyref

\usepackage{prettyref}

\newrefformat{fig}{Figure~\ref{#1}}
\newrefformat{sec}{\sect\ref{#1}}
\newrefformat{eq}{equation~\eqref{#1}}
\newrefformat{prob}{Problem~\ref{#1}}
\newrefformat{tab}{Table~\ref{#1}}
\newrefformat{thm}{Theorem~\ref{#1}}
\newrefformat{lem}{Lemma~\ref{#1}}
\newrefformat{prop}{Proposition~\ref{#1}}
\newrefformat{defn}{Definition~\ref{#1}}
\newrefformat{cor}{Corollary~\ref{#1}}
\newcommand{\pref}[1]{\prettyref{#1}}

% \Pref is just like \pref but it uppercases the first letter; for use
% at the beginning of a sentence.
\newcommand{\Pref}[1]{%
  \expandafter\ifx\csname r@@#1\endcsname\relax {\scriptsize[ref]}
    \else
    \edef\reftext{\prettyref{#1}}\expandafter\MakeUppercase\reftext
    \fi
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Comments

% big, top-level (verbatim) comments

\specialcomment{todoP}{\begingroup\color{red}TODO: }{\endgroup}

% quick (inline) comments

\newif\ifcomments\commentstrue

\ifcomments
\newcommand{\authornote}[3]{\textcolor{#1}{[#3 ---#2]}}
\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}
\else
\newcommand{\authornote}[3]{}
\newcommand{\todo}[1]{}
\fi

\newcommand{\bay}[1]{\authornote{blue}{BAY}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Semantic markup

\newcommand{\eg}{\emph{e.g.}\xspace}
\newcommand{\ie}{\emph{i.e.}\xspace}
\newcommand{\etal}{\emph{et al.}\xspace}

\newcommand{\term}[1]{\emph{#1}}

\newcommand{\pkg}[1]{\textsf{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

%\thispagestyle{empty}

\title{Functional \pkg{active} programming}
\subtitle{Demonstration proposal}

\authorinfo{Andy Gill}
{Information and Telecommunication Technology Center \\ The University of Kansas \\
Lawrence, Kansas, USA}
{andygill@@ittc.ku.edu}

\authorinfo{Brent A. Yorgey}
{Dept. of Computer and Information Science\\ The University of Pennsylvania\\
Philadelphia, Pennsylvania, USA}
{byorgey@@cis.upenn.edu}

\preprintfooter{Submitted to FARM 2013}

\maketitle

\section{Introduction}

We present \pkg{active}, a domain-specific language for functional
animation, embedded in the Haskell programming language, and inspired
by ideas from functional reactive
programming~\cite{elliott1997functional, Elliott2009:push-pull-frp}. It omits,
however, any notion of reactivity---hence \emph{functional active
  programming}.  Omitting reactivity vastly simplifies matters, but
still leaves plenty of interesting structure to exploit.

\section{Semantics}

The \pkg{active} library is centered around the two familiar
operations of sequential and parallel composition.  However, rather
than taking these operations as algebraic primitives and leaving
active values opaque, as in the approach of
\citet{hudak2004algebraic}, we take inspiration from functional
reactive programming ``behaviors''~\cite{elliott1997functional}
and from the work of~\citet{matlage2011every} in
making the semantics of active values \emph{functions} |t -> a| from
some \emph{interval} of time to some underlying type |a|.

The novel contribution of \pkg{active} is the recognition that
\emph{sequential and parallel composition operate on different types}.
In particular, parallel composition operates on active values as
described above; the resulting value is defined on the
\emph{intersection} of the input intervals.

\begin{center}
\begin{diagram}[width=140]
import ActiveDiagrams
as :: Diagram Cairo R2
as = cat' unitY with {sep = 0.5} [a12, a2, a1]
dia = (   vrule (height as) # translateX (-1)
       <> vrule (height as) # translateX 3
      )
      # alignB # translateY (-1.5)
      # lw 0.1 # dashing [0.3,0.2] 0
   <> as
   <> tl
\end{diagram}
\end{center}

Sequential composition, on the other hand, operates on
\emph{equivalence classes} of active values under translation in time,
which have a \emph{duration} but no fixed start and end times.

\begin{center}
\begin{diagram}[width=140]
import ActiveDiagrams

dia = vcat' with {sep = 1}
      [ hcat' with {sep = 2}
        [ activeD (-3) 1 red
        , seqR
        , activeD (-4) 3 blue
        ] # centerX
      , text' "="
      , result # centerX <> phantom tl
      ]

result = (draw $ active' (-3) 8 (activeRect (-3) 1 red |||||| activeRect 1 8 blue))
\end{diagram}
\end{center}
%$

This distinction allows both parallel and sequential composition to
form monoid structures on their respective types.  \pkg{active} also
has several other novel features:

\begin{itemize}
\item A careful analysis of the behavior of active values at the
  endpoints of their intervals, which we track via the type system.
\item The ability to deal cleanly with half- or fully-infinite
  intervals.  This feature in particular is quite useful in practice,
  \eg\ for composing an infinite animated ``background'' with some
  other finite animation of unknown length.
\end{itemize}

\section{Applications}

Our strong semantic foundation gives a pleasing and powerful API for
constructing animations.  There are many applications for such a
time-centric domain specific language.  We have two in mind, both of
which will be presented in the demonstration.

First, \pkg{active} can be used as a supporting DSL for
\pkg{diagrams}, a shallow DSL for drawing functionally-described
diagrams. Such a DSL stack allows for offline frame-by-frame scripting
of animations.  We have been using an earlier version of
\pkg{active}~\cite{yorgey2011active} to animate and document
\pkg{diagrams} for a while now.

Second, with a careful construction, our \pkg{active} DSL can be used
in conjunction with a deep DSL to construct a deeply embedded function
from time to values.  This allows the animation sequence to be
exported to another computation engine. Using \pkg{active} with
\pkg{Sunroof}, a deep DSL for JavaScript, we will demonstrate
how real-time browser-side animations can be built.


% {\centering
% \vspace{0.05in}
% \includegraphics[width=0.33\columnwidth]{C.png}~%
% \includegraphics[width=0.33\columnwidth]{A.png}~%
% \includegraphics[width=0.33\columnwidth]{D.png}~%
% }

% \noindent
% (Example of a tic-tac-toe animation DSL, built on top of active
\begin{figure}[h]
  \centering
\includegraphics[width=0.33\columnwidth]{C.png}~%
\includegraphics[width=0.33\columnwidth]{A.png}~%
\includegraphics[width=0.33\columnwidth]{D.png}~%
  \caption{Example of a tic-tac-toe animation built on top of \pkg{active}}
  \label{fig:tic-tac-toe}
\end{figure}

\bibliographystyle{plainnat}
\bibliography{abstract}

\end{document}
