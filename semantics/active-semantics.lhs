\documentclass{article}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

\newcommand{\cons}[1]{\mathsf{#1}}

%format inf = "\infty"
%format max = "\cons{max}"
%format min = "\cons{min}"

%format a1
%format a2
%format <> = "\diamond"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{latexsym}
\usepackage{amssymb}
\usepackage{stmaryrd}
\usepackage{proof}
\usepackage{url}
\usepackage{xspace}
\usepackage{xcolor}
\usepackage[all]{xy}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Diagrams

\usepackage{graphicx}
\usepackage[outputdir=diagrams/]{diagrams-latex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math typesetting

% Use sans-serif for math operators
\DeclareSymbolFont{sfoperators}{OT1}{cmss}{m}{n}
\DeclareSymbolFontAlphabet{\mathsf}{sfoperators}

\makeatletter
\def\operator@@font{\mathgroup\symsfoperators}
\makeatother

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
%% Semantic markup

\newcommand{\eg}{\emph{e.g.}\xspace}
\newcommand{\ie}{\emph{i.e.}\xspace}

\newcommand{\term}[1]{\emph{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\title{Active semantics}

\section{XActive}
\label{sec:XActive}

As a starting point\footnote{a refined version is presented in section
  ??}, we define the semantics of |XActive| as follows:

\begin{spec}
XActive t a = (-inf + t, t -> a, t + inf)
\end{spec}

\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams
dia = draw (xactive (-4) 6 red) <> timeline (-10) 10
\end{diagram}
\end{center}

The semantics of |XActive| is a triple of values $(t_s, f, t_e)$,
consisting of
\begin{itemize}
\item an absolute start time $t_s$ (possibly $-\infty$),
\item a function $f$ from time to values, and
\item an absolute end time $t_e$ (possibly $\infty$).
\end{itemize}
The function $f$ is only defined
on the interval $[t_s, t_e]$ (if $t_s > t_e$ we take $[t_s, t_e]$ to
represent the empty interval).

If |a| is a |Monoid|, then |XActive| also has a |Monoid| instance
which is the product of three monoids: the |(max, -inf)| monoid for
start times, the usual lifted monoid for functions, and the |(min,
inf)| monoid for end times.  This means that the interval of |a1 <>
a2| is the \emph{intersection} of the intervals of |a1| and |a2|.
Indeed, outside the intersection of their intervals, one or both is
undefined.

One could also imagine taking the union of intervals instead of the
intersection.
\begin{itemize}
\item When intervals overlap this is not too big of a problem.  But
  if intervals do not overlap we have a problem.  Either need more
  complex notion of interval (i.e. arbitrary set of intervals), or
  take smallest interval containing both, but then we need to be able
  to make up default value for a.
\item Can be derived from |Applicative|.  For |Applicative| we really
  need intersection not union, because of definedness.
\end{itemize}


% type FixedActive t a = (-inf + t, t -> a, t + inf)
%   -- closed, i.e. defined on x <= t <= y.
%   -- undefined outside the interval.

%   -- Semigroup and Monoid for this reqiure Semigroup and Monoid for a.

%   -- Have Applicative for this.

% type FreeActive t a = (d, t -> a)
%   -- d \in [0 .. inf)   t in [0, d)

%   -- Semigroup and Monoid for this do NOT require Semigroup and Monoid
%   -- for a.

%   -- No Applicative.


% data Bound1 = Inf | Closed

% type XActive (l :: Bound1) (r :: Bound1) t a = ...
% -- combination take minimum (stacking)
% (<>) :: XActive l1 r1 t a ->  XActive l2 r2 t a ->  XActive (MIN l1 l2) (MAX r1
% +r2) t a

% ((Additional: perhaps we just have two types here
%    XInfActive   -- Which *is* a Behavior
%    XActive --

% This would simply things
%   * less phantoms floating around.
%   * Only XActive would map to FActive.
% ))

% data Bound2 = Inf | Closed | Open       -- Bound is a kind

% -- type d = Diff t in this type
% type FActive (l :: Bound2) (r :: Bound2) d a =
% -- combination sequences them (beside)
% (<>) :: (Join r1 r2) => XActive l1 r1 t a ->  XActive l2 r2 t a ->  XActive l1
% +r2 t a

% I like the phantoms here.

% ((Additional:: perhaps FActive should only be finite???))



\end{document}
