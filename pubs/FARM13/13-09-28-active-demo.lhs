%% -*- LaTeX -*-
\documentclass[xcolor=svgnames,12pt]{beamer}

\newcommand{\pkg}[1]{\texttt{#1}}

\newcommand{\ty}[1]{\mathsf{#1}}
\newcommand{\con}[1]{{\color{blue}\mathsf{#1}}}
\newcommand{\consyml}[1]{\mathrel{\con{\mathord{#1}}}}
\newcommand{\consym}[1]{\mathrel{\con{\mathord{#1}}}}
\newcommand{\id}[1]{\mathit{#1}}
\newcommand{\tyid}[1]{{\color{blue}\mathit{#1}}}
\newcommand{\keyw}[1]{\mathbf{#1}}
\newcommand{\tycon}[1]{{\color{blue}\ty{#1}}}
\newcommand{\tyconsyml}[1]{\mathrel{\tycon{\mathord{#1}}}}
\newcommand{\tyconsym}[1]{\mathrel{\tycon{\mathord{#1}}}}
\newcommand{\tycls}[1]{{\color{darkgreen}\ty{#1}}}
\colorlet{darkgreen}{green!50!black}
\newcommand{\kind}[1]{{\color{darkgreen}\ty{#1}}}
\newcommand{\fun}[1]{\mathsf{#1}}
\colorlet{darkpurple}{purple!70!blue}

\colorlet{memptyC}{gray}
\colorlet{mappendC}{darkpurple}

\newcommand{\mplus}{\mathbin{\color{mappendC}{+}}}
\newcommand{\mzero}{{\color{memptyC}{0}}}

%include polycode.fmt
%include lhs2TeX-extra.fmt

%format Active = "\ty{Active}"

%format Fixed  = "\ty{Fixed}"
%format Free  = "\ty{Free}"

%format C = "\ty{C}"
%format O = "\ty{O}"
%format I = "\ty{I}"

%format parA = "\fun{parA}"
%format seqA = "\fun{seqA}"

%format memptyL = "{\color{memptyC}{\mathit{mempty}}}"
%format mappendL = "{\color{mappendC}{\mathit{mappend}}}"

%format mempty  = "{\color{memptyC}{\varepsilon}}"
%format mappend = "{\color{mappendC}{(\diamond)}}"
%format `mappend` = <>
%format <> = "\mathbin{\color{mappendC}{\diamond}}"

%format mconcat = "{\color{mappendC}{\mathit{mconcat}}}"

%format MONOID = "{\colorlet{darkgreen}{red}\tycls{Monoid}}"

%format MaybeR = "{\color{red}{\mathsf{Maybe}}}"

%format R = "\mathbb{R}"

%format ++ = "\mathbin{\color{mappendC}\plus}"
%format LL  = "{\color{memptyC} [}"
%format RR  = "{\color{memptyC} ]}"
%format ZZ  = "\mzero"
%format PP  = "\mplus"

%format a1
%format a2
%format b1
%format b2
%format d1
%format d2
%format x1
%format x2
%format y1
%format y2
%format V2

\renewcommand{\onelinecomment}{\quad--- \itshape}
\renewcommand{\Varid}[1]{{\mathit{#1}}}

% \setbeamertemplate{footline}{\insertframenumber}

\setbeamertemplate{items}[circle]

\mode<presentation>
{
  \usetheme{default}                          % use a default (plain) theme

  \setbeamertemplate{navigation symbols}{}    % don't show navigation
                                              % buttons along the
                                              % bottom
  \setbeamerfont{normal text}{family=\sffamily}

  % XXX remove this before giving actual talk!
  \setbeamertemplate{footline}[frame number]
  % {%
  %   \begin{beamercolorbox}{section in head/foot}
  %     \vskip2pt
  %     \hfill \insertframenumber
  %     \vskip2pt
  %   \end{beamercolorbox}
  % }

  \AtBeginSection[]
  {
    \begin{frame}<beamer>
      \frametitle{}
      \begin{center}
        {\Huge \insertsectionhead}
      \end{center}
    \end{frame}
  }
}

\defbeamertemplate*{title page}{customized}[1][]
{
  \vbox{}
  \vfill
  \begin{centering}
    \begin{beamercolorbox}[sep=8pt,center,#1]{title}
      \usebeamerfont{title}\inserttitle\par%
      \ifx\insertsubtitle\@@empty%
      \else%
        \vskip0.25em%
        {\usebeamerfont{subtitle}\usebeamercolor[fg]{subtitle}\insertsubtitle\par}%
      \fi%
    \end{beamercolorbox}%
    \vskip1em\par
    {\usebeamercolor[fg]{titlegraphic}\inserttitlegraphic\par}
    \vskip1em\par
    \begin{beamercolorbox}[sep=8pt,center,#1]{author}
      \usebeamerfont{author}\insertauthor
    \end{beamercolorbox}
    \begin{beamercolorbox}[sep=8pt,center,#1]{institute}
      \usebeamerfont{institute}\insertinstitute
    \end{beamercolorbox}
    \begin{beamercolorbox}[sep=8pt,center,#1]{date}
      \usebeamerfont{date}\insertdate
    \end{beamercolorbox}
  \end{centering}
  \vfill
}

% uncomment me to get 4 slides per page for printing
% \usepackage{pgfpages}
% \pgfpagesuselayout{4 on 1}[uspaper, border shrink=5mm]

% \setbeameroption{show only notes}

\usepackage[english]{babel}
\usepackage{graphicx}
\usepackage{ulem}
\usepackage{url}
\usepackage{fancyvrb}

\usepackage[outputdir=diagrams/]{diagrams-latex}

\graphicspath{{images/}}

\renewcommand{\emph}{\textbf}

\title{Functional Active Animation}
\date{FARM \\ Boston, Massachusetts, USA \\ September 28, 2013}
\author{Brent Yorgey \inst{1} \and Andy Gill \inst{2}}
\institute{\inst{1} University of Pennsylvania \and \inst{2}
  University of Kansas}
% \titlegraphic{\includegraphics[width=2in]{assoc}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

% XXX insert some pictures and/or logos?
\begin{frame}[fragile]
   \titlepage
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}[fragile]{Time-varying values}

\begin{diagram}[width=300]
import ActiveDiagrams

dia
  = mconcat
    [ wiggle (closedEP (-3)) (closedEP 6)
    , timeline (-10) 10
    ]
    # centerXY # pad 1.1
\end{diagram}

  \[ t \times (t \to a) \times t \]

  \begin{center}
    {{\scriptsize Matlage, Kevin, and Andy Gill. \textit{Every
          Animation Should Have a Beginning, a Middle, and an
          End}. TFP, 2011, pp. 150-165.}}
  \end{center}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Operations?}
  \begin{center}
    \includegraphics[width=3in]{operation}
  \end{center}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}[fragile]{Operations?}
\begin{center}
\begin{diagram}[width=300]
import ActiveDiagrams

dia = timeline (-10) 10 <> wiggle (openEP (-3)) (closedEP 6)
\end{diagram}
\end{center}

  % XXX sequential composition picture

  \onslide<2>
  Semantics?
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}
  \begin{center}
    \includegraphics[width=2in]{alice-rabbithole.jpg}
  \end{center}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Generalizations}

Infinite endpoints

% XXX picture
\end{frame}

\begin{frame}{Generalizations}

  Open/closed endpoints

% XXX picture
\end{frame}

\begin{frame}{Generalizations}

  Sequential composition acts on \emph{equivalence classes} under translation

% XXX picture

\end{frame}

\begin{frame}{Types}
  \[ |Active f l r t a| \]
  \begin{itemize}
  \item |f|: |Fixed| or |Free|
  \item |l, r|: |O|, |C|, or |I|nfinite
  \item |t|: time
  \item |a|: values
  \end{itemize}
\end{frame}

\begin{frame}{Examples}
  \begin{multline*}
   |parA :: (Semigroup a, Ord t)| \\
   |=> Active Fixed l r t a -> Active Fixed l' r' t a| \\
   |-> Active Fixed (Isect l l') (Isect r r') t a |
  \end{multline*}
  \onslide<2>
  \begin{multline*}
   |seqA :: (Clock t, Compat r1 l2)| \\
   |=> Active Free l1 r1 t a -> Active Free l2 r2 t a| \\
   |-> Active Free l1 r2 t a|
  \end{multline*}
\end{frame}

\begin{frame}{Practical difficulties}
  \begin{itemize}
  \item Really want dependent types sometimes
  \item How to present usable yet precise API?
  \end{itemize}
\end{frame}

\begin{frame}
  \begin{center}
    {\Huge Demo!}
  \end{center}
\end{frame}

\end{document}
