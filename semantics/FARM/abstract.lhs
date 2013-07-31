%% -*- LaTeX -*-

\documentclass[9pt,preprint,authoryear]{sigplanconf}

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
\usepackage[outputdir=diagrams/,backend=ps,extension=eps]{diagrams-latex}

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

\title{Functional \pkg{active} programming}
\subtitle{Demonstration proposal}

\authorinfo{Brent A. Yorgey}
{Dept. of Computer and Information Science\\ The University of Pennsylvania\\
Philadelphia, Pennsylvania, USA}
{byorgey@@cis.upenn.edu}

\authorinfo{Andy Gill}
{XXX department \\ The University of Kansas \\
Lawrence, Kansas, USA}
{XXX email}

\preprintfooter{Submitted to FARM 2013}

\maketitle

\section{Introduction}

We present \pkg{active}, a domain-specific language for functional
animation, embedded in the Haskell programming
language~\cite{haskell}, and inspired by ideas from functional
reactive programming~\cite{frp}. It omits, however, any notion of
reactivity---hence \emph{functional active programming}.

Omitting reactivity vastly simplifies matters, but still leaves plenty
to chew on.

\section{Semantics}

The \pkg{active} library is centered around the two familiar
operations of sequential and parallel composition.  However, rather
than taking these operations as algebraic primitives and leaving
active values opaque, as in the approach of
\cite{hudak-temporal-media}, we take inspiration from functional
reactive programming ``behaviors''~\cite{frp} in making the semantics
of active values \emph{functions} |t -> a| from time to some
underlying type |a|.

\begin{todoP}
  \begin{itemize}
  \item (potentially infinite) start and end times
  \item seq. and par. comp operate on different types
  \item e.g. this is what makes infinite start + end times possible
  \item some nice pictures?
  \end{itemize}
\end{todoP}

\section{Applications}

\begin{todoP}
  Strong semantic foundation gives a pleasing and powerful API for
  constructing animations.  We will demonstrate several examples.
  \begin{itemize}
  \item animations with \pkg{diagrams}
  \item Abstracting over the time type allows for deep
    embeddings---compilation to JS---animations in the browser
  \end{itemize}
\end{todoP}

\bibliographystyle{plainnat}
\bibliography{abstract}

\end{document}
