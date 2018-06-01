% -*- mode: LaTeX; compile-command: "./build.sh" -*-

%% For double-blind review submission, w/o CCS and ACM Reference (max submission space)
\documentclass[sigplan,10pt,review,anonymous]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For double-blind review submission, w/ CCS and ACM Reference
%\documentclass[sigplan,10pt,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission, w/o CCS and ACM Reference (max submission space)
%\documentclass[sigplan,10pt,review]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For single-blind review submission, w/ CCS and ACM Reference
%\documentclass[sigplan,10pt,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission, w/ required CCS and ACM Reference
%\documentclass[sigplan,10pt]{acmart}\settopmatter{}


%% Conference information
%% Supplied to authors by publisher for camera-ready submission;
%% use defaults for review submission.
\acmConference[FARM'18]{ACM SIGPLAN Workshop on Functional Art, Music,
Modelling, and Design}{September 29, 2018}{St.\ Louis, MO, USA}
\acmYear{2018}
\acmISBN{} % \acmISBN{978-x-xxxx-xxxx-x/YY/MM}
\acmDOI{} % \acmDOI{10.1145/nnnnnnn.nnnnnnn}
\startPage{1}

%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission;
%% use 'none' for review submission.
\setcopyright{none}
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2017}           %% If different from \acmYear

%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
%% Citation style
\citestyle{acmauthoryear}  %% For author/year citations

%% Some recommended packages.
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption} %% For complex figures with subfigures/subcaptions
                        %% http://ctan.org/pkg/subcaption

\usepackage{xspace}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX formatting
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include polycode.fmt

%format <$> = "\mathbin{\langle \$ \rangle}"
%format <#> = "\mathbin{\langle \# \rangle}"
%format Rational = "\mathbb{Q}"

%format ->- = "\mathbin{-\!\!\!>\!\!\!-}"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% LaTeX formatting
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{latexsym}
\usepackage{amssymb}
\usepackage{stmaryrd}
\usepackage{url}
\usepackage{xspace}
\usepackage{xcolor}
\usepackage[all]{xy}
\usepackage{breakurl}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Diagrams

\usepackage{pgf}
\usepackage{graphicx}
\usepackage[outputdir=diagrams,backend=pgf,extension=pgf,input]{diagrams-latex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Prettyref

\usepackage{prettyref}

\newrefformat{fig}{Figure~\ref{#1}}
\newrefformat{sec}{\Sect\ref{#1}}
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

\newif\ifcomments\commentstrue
%\newif\ifcomments\commentsfalse

\ifcomments
\newcommand{\personalnote}[3]{\textcolor{#1}{[#3 ---#2]}}
\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}
\newcommand{\tocite}{\todo{add citation}}
\newcommand{\needsdia}{\todo{add illustration}}
\else
\newcommand{\personalnote}[3]{}
\newcommand{\todo}[1]{}
\fi

\newcommand{\bay}[1]{\personalnote{blue}{BAY}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Semantic markup

\newcommand{\eg}{\latin{e.g.}\xspace}
\newcommand{\ie}{\latin{i.e.}\xspace}
\newcommand{\etal}{\latin{et al.}\xspace}
\newcommand{\etc}{\latin{etc.}\xspace}

\newcommand{\term}[1]{\emph{#1}}
\newcommand{\latin}[1]{\textit{#1}}
\newcommand{\foreign}[1]{\emph{#1}}

\newcommand{\hackage}[1]{\textsf{#1}\xspace}

\newcommand{\activelib}{\hackage{active}}
\newcommand{\diagrams}{\hackage{diagrams}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

%% Title information
\title{Active}                          %% [Short Title] is optional;
                                        %% when present, will be used in
                                        %% header instead of Full Title.
% \subtitle{Subtitle}                     %% \subtitle is optional
% \subtitlenote{with subtitle note}       %% \subtitlenote is optional;
%                                         %% can be repeated if necessary;
%                                         %% contents suppressed with 'anonymous'


%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

%% Author with single affiliation.
\author{Brent A. Yorgey}
\affiliation{
  % \position{Position1}
  \department{Dept.\ of Mathematics and Computer Science} %% \department is recommended
  \institution{Hendrix College}            %% \institution is required
%  \streetaddress{Street1 Address1}
  \city{Conway}
  \state{AR}
  \country{USA}                    %% \country is recommended
}
\email{yorgey@@hendrix.edu}          %% \email is recommended

% %% Author with two affiliations and emails.
% \author{First2 Last2}
% \authornote{with author2 note}          %% \authornote is optional;
%                                         %% can be repeated if necessary
% \orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
% \affiliation{
%   \position{Position2a}
%   \department{Department2a}             %% \department is recommended
%   \institution{Institution2a}           %% \institution is required
%   \streetaddress{Street2a Address2a}
%   \city{City2a}
%   \state{State2a}
%   \postcode{Post-Code2a}
%   \country{Country2a}                   %% \country is recommended
% }
% \email{first2.last2@inst2a.com}         %% \email is recommended
% \affiliation{
%   \position{Position2b}
%   \department{Department2b}             %% \department is recommended
%   \institution{Institution2b}           %% \institution is required
%   \streetaddress{Street3b Address2b}
%   \city{City2b}
%   \state{State2b}
%   \postcode{Post-Code2b}
%   \country{Country2b}                   %% \country is recommended
% }
% \email{first2.last2@inst2b.org}         %% \email is recommended


%% Abstract
%% Note: \begin{abstract}...\end{abstract} environment must come
%% before \maketitle command
\begin{abstract}
  We introduce \activelib, a new Haskell library and domain-specific
  language for describing \emph{time-varying values}.  Although it was
  originally designed with the goal of making animations with the
  \diagrams vector graphics framework \tocite, it is more broadly
  applicable to any sort of \todo{what? ``temporal media''?
    time-varying domain?}, such as music or sound generation,
  \todo{other examples}

  We describe the library, give examples of its use, and explain and
  justify the design decisions that went into its development.
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008</concept_id>
<concept_desc>Software and its engineering~General programming languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10003456.10003457.10003521.10003525</concept_id>
<concept_desc>Social and professional topics~History of programming languages</concept_desc>
<concept_significance>300</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~General programming languages}
\ccsdesc[300]{Social and professional topics~History of programming languages}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{keyword1, keyword2, keyword3}  %% \keywords are mandatory in final camera-ready submission


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.

\maketitle

\todo{Figure out a system for including inline active+diagrams code
  which automatically compiles to (a) a static diagram showing
  something like beginning, middle, \& end, or maybe just beginning
  and end, or maybe just a representative frame (maybe configurable)
  (b) a GIF that gets uploaded somewhere, with (c) a QR code linking
  to it!}

\section{Introduction}

\todo{Introduce with some cool examples!}

\todo{List contributions, with forward references to the rest of the
  paper.}

\todo{Upload new version of \activelib to Hackage.}
\todo{Mention \activelib is on Hackage, with link.}

\section{The |Active| type}

The core of the library is the |Active| type.  A value of type |Active
a| represents a \emph{time-varying value} of type |a|, with a given
\term{duration}.  Specifically, we can think of each |Active a| value
as having a nonnegative rational duration $d$, and a total function
$f : [0,d] \to a$ which assigns a value of type |a| to every duration
from $0$ to $d$, inclusive.  (|Active| is not actually implemented
this way; we will discuss the real implementation in section
\todo{which?}.)  The duration can also be infinite, in which case $f$
assigs a value to every $d \geq 0$.

\needsdia

This definition may seem simple, but there are nonobvious design
decisions lurking behind it which are worth pointing out. We believe
these are the choices which result in the most elegant, usable
library, but we certainly don't expect you to believe it at this
point!  We will justify each of these design decisions in more depth
throughout the paper. \todo{Include forward references to where each of
these design decisions is explained/justified.}

\begin{itemize}
\item Since the domain of $f$ is the \emph{closed} interval $[0,d]$,
  it is not possible to have an ``empty'' or ``everywhere undefined''
  |Active| value.  However, when $d = 0$ it is possible to have an
  ``instantaneous'' |Active| value defined only at a single point.
\item The domain of every |Active| value always starts at $0$. For
  example, it is not possible to make an |Active| with a domain of
  $[3,5]$.
\item Since the semantics of |Active| is a \emph{function}, an
  |Active| value is inherently continuous.  For example, we don't lose
  any ``resolution'' by zooming in.
\item The duration of an |Active| value is a \emph{rational} number.
  It is not possible to have an irrational duration or to use any type
  other than Haskell's standard |Rational| type.
\item |Active| values can extend infinitely into the future, but not
  the past.
\item It is not possible to tell whether an |Active| value is finite
  or infinite by looking at its type.  This means there are some
  combinators (such as |backwards|) which are necessarily partial,
  because they only make sense when applied to finite values.
\end{itemize}

\subsection{Constructing |Active| values}
\label{sec:constructing}

\todo{|activeF|, |activeI|, |discrete|; |instant|, |lasting|, |always|; |ui|, |dur|}

What can we do with the bare |Active| type?  First, |Active| is a
|Functor|, which means we can use
\begin{spec}
fmap :: (a -> b) -> Active a -> Active b
\end{spec}
(also known as |<$>|) % $
%
to apply a function to an |Active| value at every point in time, by
postcomposition.  The \activelib library also defines
\begin{spec}
(<#>) :: Active a -> (a -> b) -> Active b
\end{spec}
as a flipped variant of |<$>| % $
%
for convenience (we will see examples of its use later).  There is
also a collection of methods for manipulating the duration, shown in
\pref{fig:duration-functions}.

\subsection{Manipulating duration}
\label{sec:duration}

\begin{figure}
  \centering
  \begin{spec}
cut            :: Rational              ->  Active a -> Active a
cutTo          :: Active a              ->  Active a -> Active a

omit           :: Rational              ->  Active a -> Active a
slice          :: Rational -> Rational  ->  Active a -> Active a

stretch        :: Rational              ->  Active a -> Active a
stretchTo      :: Rational              ->  Active a -> Active a
matchDuration  :: Active b              ->  Active a -> Active a

backwards      ::                           Active a -> Active a
  \end{spec}
  \caption{Functions for manipulating duration}
  \label{fig:duration-functions}
\end{figure}

For example, the |cut| function corresponds to the |take| function on
lists, and truncates an |Active| value if necessary so that it has at
most the given duration.  |omit| is similar function, parallel to
|drop| on lists, and |slice| is a combination of |cut| and |omit|.
|stretch| and its variants |stretchTo| and |matchDuration| allow
``zooming in or out'' in time, stretching or compressing an |Active|
value so it becomes longer or shorter.  |backwards| switches the
beginning and end of an |Active| value---though as already mentioned
it can only be used on values with a finite duration.

We could also imagine a function
\begin{spec}
  mapDuration :: (Rational -> Rational) -> Active a -> Active a
\end{spec}
which works by precomposition with the given transformation on time.
That is, if |act :: Active a|, then |mapDuration f| would take on the
value |act (f t)| at time |t|.  \todo{cite anyone who mentions this
  function?  Does Conal mention it?}  However, we deliberately choose
not to include this function in the library, for two reasons.  First,
there is no guarantee that the given time transformation |f| will
result in values in the domain of |act|; one could imagine encoding
such an invariant via dependent types, but the contortions required to
do this in Haskell would likely render the library practically
unusable.  More importantly and subtly, however, the rest of the
library is carefully designed to allow only affine transformations on
time, and we take advantage of this to design an efficient
implementation.  If we allowed arbitrary nonlinear transformations on
time via |mapDuration|, we would be stuck representing |Active a| by
an actual function |Rational -> a|.

Note that worries about causality are \emph{not} a reason for
excluding |mapDuration|.  There is no built-in mechanism by which
previous values can determine or influence future values, and so there
is no problem with functions such as |backwards| which reverse past
and future. In some sense, \activelib can be thought of as
``functional reactive programming without the reactivity''.

\subsection{Running and sampling}
\label{sec:sampling}

\todo{|runActive|; |duration|, |start|, |end|; |samples|}.

\section{Sequential composition}
\label{sec:sequential}

\emph{Composition} must be at the heart of any DSL for constructing
complex values such as animations.  The simplest way to compose
|Active| values is \term{sequentially}, that is, running one
value followed by another. The duration of the resulting |Active| is
the sum of the input durations.

This seems simple enough in principle, but it raises a tricky issue:
what happens at the precise moment of transition?  Recall that finite
|Active| values are defined on a \emph{closed} interval $[0,d]$, that
is, the domain includes both endpoints.  So two |Active| values
composed in sequence have an instant of overlap, where both are
defined.  One way around the issue would be to instead specify that
|Active| values are only defined on the half-open interval $[0,d)$,
excluding the right endpoint.  However, while this solves the problem
for join points, it will always leave the final point of any |Active|
undefined, which seems unsatisfactory. It also has the effect of
baking in a bias for the right value at join points; while this may
seem more ``natural'' than the alternative (namely, making |Active|
values defined on $(0,d]$ and thus preferring the left value at join
points), it is still somewhat arbitrary, and we would like to avoid
baking arbitrary choices into our API.

Another reasonable reaction to this problem is: who cares?  Since the
point of overlap is instantaneous, the probability of sampling exactly
at that point is essentially zero, and besides, even if we do sample
at exactly that point, does it really matter whether a single sample
comes from the left or right |Active|?  Indeed, \todo{mention that
  previous systems (Hudak, Elliot?, Matlage?) all punt on this issue.}

Perhaps these issues don't matter for some domains with high sampling
rates, such as audio.  However, they can matter a lot for other
domains.  First of all, the argument that we have zero probability of
sampling exactly at a transition point is spurious, since it is
reasonable---and common---to sample at a rate which evenly divides the
durations used in constructing an |Active|.  For example, we might
sequence values lasting one second, and then sample at a rate of 30
per second.  Second, in some domains we may indeed care to control the
precise sample at the transition between two |Active| values---and not
just by picking one value or the other, but perhaps by combining the
value from the end of the first |Active| with the value at the start
of the second.  For example, when building a musical score, we might
want the final chord of a repeating motif to sound on the downbeat,
just as another voice enters with the beginning of a new melody.  Or
when building an animation with one shape disappearing exactly as a
new shape appears, it might look less jarring to have one frame where
both shapes are visible simultaneously.

Put simply, sequential transition points are not just incidental
details to be swept under a rug, but key moments in time that we want
to be able to control explicitly.  The solution is simple: we give the
programmer control over what happens at transition points by requiring
a |Semigroup| instance on the underlying type.
\begin{spec}
(->-) :: Semigroup a => Active a -> Active a -> Active a
\end{spec}
\todo{Recall definition of |Semigroup|.  Talk about |First| and
  |Last|, convenience operators.}

\section{Parallel composition}
\label{sec:parallel}

\section{Other modes of composition}
\label{sec:other-composition}

\todo{e.g. Composition via anchors? Composition via explicit start and
  end times?  Show how these can be encoded in terms of more
  fundamental composition operations.}

\section{An extended example}
\label{sec:example}

\todo{Come up with a cool extended example!}

\section{Linear sampling}
\label{sec:linear-sampling}

\todo{Show problems with left-nested sequencing.  If we can get it to
  work in time---and it's actually faster!---show how to use deep
  embedding to speed up sampling.}

\section{Related work}
\label{sec:related-work}

\todo{Related work to discuss: Hudak (Polymorphic Temporal Media),
  Elliot (Tangible Functional Programming?), Matlage \& Gill
  (Beginning, Middle, and End), Janin (T-calculus, LiveTiles); others?}

%% Acknowledgments
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
  This material is based upon work supported by the
  \grantsponsor{GS100000001}{National Science
    Foundation}{http://dx.doi.org/10.13039/100000001} under Grant
  No.~\grantnum{GS100000001}{nnnnnnn} and Grant
  No.~\grantnum{GS100000001}{mmmmmmm}.  Any opinions, findings, and
  conclusions or recommendations expressed in this material are those
  of the author and do not necessarily reflect the views of the
  National Science Foundation.
\end{acks}


%% Bibliography
%\bibliography{bibfile}


% %% Appendix
% \appendix
% \section{Appendix}

% Text of appendix \ldots

\end{document}
