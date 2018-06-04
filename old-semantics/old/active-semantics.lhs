%% -*- LaTeX -*-

\documentclass{article}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

\newcommand{\cons}[1]{\mathsf{#1}}

\newcommand{\idiom}[1]{\llbracket #1 \rrbracket}

%format const = "\cons{const}"
%format inf   = "\infty"
%format max   = "\cons{max}"
%format min   = "\cons{min}"
%format pure  = "\cons{pure}"

%format ===      = "\equiv"
%format /=       = "\neq"
%format <>       = "\diamond"
%format mempty   = "\varepsilon"
%format idiom(a) = "\idiom{" a "}"
%format <*>      = "\circledast"

%format `seqR`   = "\rhd"
%format seqR     = "(\mathord{\rhd}\!)"
%format `seqL`   = "\lhd"
%format seqL     = "(\!\mathord{\lhd})"

%format a1
%format a2
%format l1
%format l2
%format r1
%format r2

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
\usepackage{natbib}
\usepackage[all]{xy}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Comments

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
\newrefformat{sec}{\S\ref{#1}}
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

\newcommand{\pkg}[1]{\texttt{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\title{|Active| semantics}
\author{Brent Yorgey \and Andy Gill \and Ed Komp}

\maketitle

\section{Introduction}
\label{sec:active}

Taking our cue from \citet{matlage2011every}, we start with the
following preliminary semantics for |Active|, a time-varying value
with a beginning, middle, and end:

\begin{spec}
Active t a === (t, t -> a, t)
\end{spec}

\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams
dia = a1 <> tl
\end{diagram}
\end{center}

That is, the semantics of |Active| is a triple of values $(t_s, f, t_e)$,
consisting of
\begin{itemize}
\item an absolute start time $t_s$,
\item a function $f$ from time to values, and
\item an absolute end time $t_e$.
\end{itemize}
We call |a| the \term{base type}, and $[t_s, t_e]$ the
\term{interval}.  (For now, we put off the question of where the
function is defined---we return to it in \pref{sec:why-not-union}). We
assume the type of time values $t$ is bi-infinite, has a linear order,
and forms an affine space together with an associated type $d$ of
\emph{durations}.  In particular it does not matter whether time is
continuous or discrete.  Finally, we note that |Active t| is a
|Functor|.

This is our starting point, but over the remainder of this document we
will greatly refine it.  In particular:
\begin{itemize}
\item We argue that parallel composition of |Active| values should
  work by taking an \emph{intersection} of intervals, which to our
  knowledge has not previously been considered.
\item We extend |Active| to allow for \emph{infinite} time-varying
  values---indeed, this falls out naturally from considering the
  semantics of parallel composition.
 % \todo{is this a novel
 %    contribution?  The idea of infinite time-varying values is not
 %    hard to come up with, but making it work nicely depends crucially
 %    on the other refinements listed below; in particular, recognizing
 %    the distinction between |XActive| and |FActive|.}
\item In order to endow sequential composition with the proper
  semantics, we introduce a more refined way to keep track of what
  happens at the endpoints of intervals.
\item Most consequentially, we show that in fact parallel and
  sequential composition most naturally act on \emph{two different
    types}, and we will accordingly split |Active| into two types,
  |XActive| and |FActive|, where |FActive| abstractly consists of
  \emph{equivalence classes} of |XActive| values under translation in
  time.
\item We then show how to convert back and forth between |XActive| and
  |FActive|, and in particular how to enforce that the user may only
  use |FActive| values as if they were equivalence classes, even
  though concretely one must compute not with equivalence classes but
  with representatives.
\end{itemize}

\section{Parallel composition}
\label{sec:par-comp}

It is well-known that there are two fundamental modes of composition
for time-varying values: \emph{parallel composition} (\ie\ performing
two time-varying values simultaneously) and \emph{sequential
  composition} (\ie\ performing two time-varying values one after the
other).  Ultimately, our refinements to |Active| all have their root
in the semantics of one or the other. We begin with parallel
composition.

\subsection{Parallel composition as a monoid}
\label{sec:par-monoid}

If two |Active| values happen to
have the same interval, it is clear how their parallel composition
ought to work: just just combine their values pointwise (of course,
this requires a semigroup structure on the base type), resulting in
another |Active| value with the same interval.

\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams
as :: Diagram Cairo R2
as = cat' unitY with {sep = 0.5}
   [ draw (active' (-6) 3 (activeRect (-6) 3 red <> activeRect (-6) 3 blue))
   , activeD (-6) 3 blue
   , activeD (-6) 3 red
   ]

dia = as <> tl
\end{diagram}
\end{center}

However, what should be done when the intervals do not match?  We
could simply \emph{require} matching intervals, but making parallel
composition a partial operation seems like an ugly cop-out.  In
practice, it would probably require lots of tedious interval-fiddling
to make things line up before composing.

Once we are committed to defining parallel composition on |Active|
values with non-matching intervals, the next question arises
naturally: how should the interval of the output |Active| be
determined from those of the inputs?  There are really only two
sensible choices: to take the \emph{union} of the intervals (\ie
the smallest interval which contains both) or the \emph{intersection}
(\ie the largest which is contained in both).

Our novel contribution is to take the intersection, rather than the
union as in some past approaches~\citep{matlage2011every,
  yorgey2011active}.  At first blush union might seem more useful, but
we argue in the following section (\pref{sec:why-not-union}) why
intersection gives us a cleaner and more useful semantics.

Given a semigroup structure on the type |a|, we can now define the
parallel composition |(a1 <> a2)| of two |Active t a| values as the
value whose interval is the intersection of the intervals of |a1| and
|a2|, with values generated by combining the values of |a1| and |a2|
pointwise (which is well-defined since, by definition, both |a1| and
|a2| are defined everywhere on the intersection of their intervals).
\begin{center}
\begin{diagram}[width=200]
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
Abstractly, we can construct parallel composition as the product of
semigroup structures on the three components of |Active|: namely, the
|max| semigroup for start times, the usual lifted semigroup for
functions, and the |min| semigroup for end times.  This means that
parallel composition automatically forms a semigroup.

The next natural question is whether we can extend this semigroup to a
monoid.  On the face of it, we are stymied by the fact that |max| and
|min| on $t$ do not have identity elements, since we have assumed that
$t$ is bi-infinite.  However, this suggests adjoining distinguished
identity elements to the start and end types:
\begin{spec}
type Active t a = (-inf + t, t -> a, t + inf)
\end{spec}
\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams
dia = a1R <> tl
\end{diagram}
\end{center}
That is, instead of being limited to finite start and end times as in
our initial semantics, an |Active| value may now potentially ``start
at time |-inf|'' (that is, be defined for all values of $t \leq t_e$)
and/or ``end at time |inf|''.  Now we can construct a parallel
composition monoid on |Active| as the product of monoids for its
components; the identity element for parallel composition is thus
given by |(-inf, const mempty, inf)|, that is, the |Active| which is
constantly the identity value at all times.

\subsection{Parallel composition as an applicative functor}
\label{sec:par-applicative}

So far we have seen that |Active t a| has a monoid structure
corresponding to parallel composition (as long as |a| has a monoid
structure).  However, more is true: parallel composition in fact gives
rise to an applicative functor structure for |Active t|.  |pure :: a
-> Active t a| generates a bi-infinite, constant |Active| value;
|(<*>) :: Active t (a -> b) -> Active t a -> Active t b| applies
functions to values pointwise on the intersection of the two
intervals.  Note that neither of these operations require any
constraints on |a| or |b|.

It is not hard to verify that this definition satisfies the usual laws
for |Applicative|; but in fact we don't need to.  Instead, we need
only note that it can be built compositionally from the well-known
|Applicative| instance for functions and two applications of the
standard pairing construction (known as |Writer| in the Haskell
standard libraries) which creates an |Applicative| instance
for |(w,) . f| given an |Applicative| instance for |f| and a |Monoid|
on |w|.

As usual, the |Applicative| instance is more fundamental than the
|Monoid| instance, in the sense that we can recover the latter from
the former.  In particular, we may take |mempty = pure mempty| and |a1
<> a2 = idiom(a1 <> a2)| (where |idiom(-)| are \emph{idiom
  brackets}~\cite{applicative}).

\section{Why not union?}
\label{sec:why-not-union}

\citet{matlage2011every} explicitly take the \emph{union} of intervals
(to be precise, the smallest interval containing both input intervals)
when forming the parallel composition of two |Active| values.  Earlier
versions of the \pkg{active} library~\citep{yorgey2011active} made the
same choice.  Indeed, on the face of it, taking the union seems more
``useful'': one typically wants to compose animations out of disparate
parts which do not all cover the same interval.  For example, I might
want to have a circle moving across the screen, and then when it is
halfway something else appears and does something\dots and so on.
This sounds exactly like a union semantics for parallel composition.
However, as we will show later, using our semantics, one \emph{can}
compose things in this sort of ``uniony'' way, but it ends up being a
derived operation, and should not be taken as \emph{primitive}.
Ultimately this is a good thing, because it gives the user more
control over how the unioning happens.  In the end, we have come to
the conclusion that taking the intersection of intervals gives a
cleaner, more natural, and ultimately more useful semantics.  We can
justify this decision in a few different ways.

First, the natural identity element for parallel composition based on
union would be something like |(+inf, const mempty, -inf)|, which is
nonsense.  In practice we end up adjoining a new, distinguished
identity element, leading to the need for many special-case analyses
to handle it appropriately.  On the other hand, as we have seen above,
the natural identity element for intersection has a natural
interpretation, and needs no special cases.

Second, combining via union forces us to decide what values should be
used \emph{outside} the interval of an active value, since we may need
a value to combine.
\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams
dia = (cat' unitY with [a1X,a2X]) <> tl

a2X = mconcat
  [ a2
  , text' "?" # scale 0.7 # translateX (-3.5)
  , activeRect (-6) (-1) (blend 0.7 blue white)
  ]

a1X = mconcat
  [ a1
  , text' "?" # scale 0.7 # translateX 4
  , activeRect 3 5 (blend 0.5 red white)
  ]
\end{diagram}
\end{center}
We have a few choices:

\begin{itemize}
\item One seemingly sensible choice is |mempty|, which works as long
  as there is a |Monoid| instance for the base type |a|.  However,
  more generally, we want not only a monoidal parallel composition
  operation, but also an |Applicative| instance for active values
  (from which parallel composition can be derived).  Unlike parallel
  composition itself, the |Applicative| instance cannot depend
  on |Monoid| instances for the base types.

\item Another option (the one taken by~\citet{matlage2011every}) is to
  ``clamp'' the value of the function to its value at the endpoints of
  the interval, \ie\ $f(t) = f(t_s)$ for all $t < t_s$ and $f(t) =
  f(t_e)$ for all $t > t_e$.  However, this seems somewhat ad-hoc and
  may not always be what the user wants.

\item A final option (taken by earlier versions of the \pkg{active}
  package) is to simply require that the function be defined for all
  values of $t$ in the first place.  However, this requires the user
  to reason about the behavior of active values over the whole
  timeline and not just on their interval, in some sense defeating the
  point of having an interval in the first place.
\end{itemize}

The point is that there are multiple viable options, with no one
option standing out as obviously the most correct or fundamental.
This in and of itself is a strong hint that union should not be
taken as primitive.  It is easy to imagine users wanting all three
of the behaviors described above; baking any one of them into the
primitive semantics of parallel composition necessitates awkward
workarounds when the user wants a different behavior.

We can also see that taking intersection instead of union makes the
semantics of |Active| simpler: under unioning parallel composition,
the semantics of |Active| must somehow include the values the function
takes on outside the interval; under intersecting parallel
composition, we may simply state that the function is undefined
outside the interval.

It should be noted that as far as expressiveness goes, intersection
versus union does not matter that much: given appropriate extension
and restriction operations to modify the intervals of |Active| values,
unioning and intersecting parallel composition are inter-definable.

\section{Sequential composition}
\label{sec:seq-comp}

We now turn to sequential composition. The basic idea, of course, is
that the end time of one |Active| should be matched up with the start
time of another, creating one long |Active| value which behaves first
like one and then the other.\footnote{The astute reader will already
  be wondering about values with infinite start or end times.  We will
  return to deal with that complication shortly.}
\begin{center}
\begin{diagram}[width=200]
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
However, this clear intuition has two big problems lurking in the details.
First, what happens at the precise time of transition between the two
values?  Second, how should the resulting composed value be positioned
in time?  We will attack each problem in turn.

\subsection{Transitions and endpoints}
\label{sec:endpoints}

When two |Active|s are composed sequentially, what value does the
resulting |Active| take on at the precise transition between the two
inputs?
\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams

dia = result # centerX <> phantom tl

result = atop (text' "?" # scale 0.7 # translateX 1). draw . active' (-3) 8 $ hcat
  [ activeRect (-3) 1 red
  , vrule 3 # lw 0.1 # dashing [0.1,0.1] 0 # lc grey
  , activeRect 1 8 blue
  ]
\end{diagram}
\end{center}
%$
The problem is that at the precise transition time we have \emph{two}
values of the base type, one from each input.  Somehow we have to pick
a single value which the composed |Active| will take on at that time.
Our options include:
\begin{itemize}
\item We could combine the two values according to some semigroup operation.
  However, this is not a very attractive option; intuitively, sequential
  composition should not require any constraints on the base type at
  all.
\item We could simply take the second value and discard the first, or
  take the first and discard the second (the latter is what previous
  versions of the \pkg{active} package did).  The problem is that this
  represents an arbitrary choice, which we should be wary of baking
  into our semantics.  As with unioning parallel composition, we take
  this as a sign that we should take something yet more primitive
  which avoids an arbitrary choice, and expose the choice to the user.
\end{itemize}

Our solution is to refine the semantics yet again. The idea is to
track \emph{whether an active value is defined at its endpoints}, and
only allow sequential composition when one |Active| is defined at the
common endpoint (it is \term{closed}) and one is not (it is
\term{open}). The semantics of |Active| will still consist of a triple
|(-inf + t, t -> a, t + inf)|.  However, we now add two type indices,
one for each endpoint, which are taken from a set
$\{\infty,|C|,|O|\}$.  They affect the meaning of the function |t ->
a|, in particular by determining where it is defined.  Their meanings
are as follows:
\begin{itemize}
\item $\infty$ means that the endpoint is \emph{infinite}, that is,
  $\pm \infty$.  Of course, we can already tell whether an endpoint is
  infinite simply by inspecting its value, but it is useful to also track
  this information at the type level, because it affects how |Active|s
  can be composed.
\item |C| means that the endpoint is \emph{closed}, that is, the
  function is defined for values up to \emph{and including} the
  endpoint.  We will continue to illustrate such endpoints with a
  solid black line.
\item |O| means that the endpoint is \emph{open}, that is, the
  function is defined for values up to \emph{but not including} the
  endpoint.  We will illustrate such endpoints using a dotted grey line.
\end{itemize}

Here are just a couple examples taken from the (nine) types which are now possible, with a
representative illustration for each:

\begin{itemize}

\item |Active O C t a|---a finite interval, closed at the right
  endpoint but open on the left.
\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams

dia = oc <> tl

oc = draw $ Active (O (-6), r, C 3)  -- $
  where
    r = activeRect (-6) 3 red
\end{diagram}
\end{center}

\item |Active inf O t a|---an open endpoint on the right, infinite on
  the left.
\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams

dia = infO <> tl

infO = draw $ Active (I, r, O 2)  -- $
  where
    r = cat' unit_X with
      [ activeRect (-2) 2 red
      , fade 7 0 0.5 50
      ]
\end{diagram}
\end{center}
\end{itemize}

Now there are two sequential composition operators, with types given by
\begin{spec}
seqR  ::  Active l1 O t a  ->  Active C r2 t a  ->  Active l1 r2 t a
seqL  ::  Active l1 C t a  ->  Active O r2 t a  ->  Active l1 r2 t a
\end{spec}

|seqR| gives rise to a semigroup structure on |Active C O t a|
(without the need for any constraints on |a|!), and similarly for
|seqL| and |Active O C t a|.

Note that this also neatly handles the problem, noted in passing
earlier, of trying to sequentially compose infinite active values.  We
can sequence, say, an |Active inf O| and |Active C O| (resulting in
|Active inf O|), but the types prevent us from sequencing, say, an
|Active C inf| with anything to its right. On the other hand, the very
astute reader will note that we have created problems for parallel
composition---we return to patch things up in \pref{sec:fix-par-comp}.

It is a bit awkward that we need two different sequential composition
operators.  In some sense, there is really only one, with a type
something like
\begin{spec}
seq  :: (r1,l2 `elem` {O,C}, r1 /= l2),
     => Active l1 r1 t a -> Active l2 r2 t a -> Active l1 r2 t a
\end{spec}
but it is not clear how best to express this type in such a way that
|seq| is convenient to use.  More abstractly, it is not clear what to
make of |seq|.  It seems like some sort of ``indexed monoid'', but it
is not quite a category (since the indices must \emph{not} match
instead of match!).

\subsection{Locations and translations}
\label{sec:locations}

We now attack the second problem: where should the result of a
sequential composition be placed in time?  Our primary motivation is
to ensure that |seqR| and |seqL| are monoidal.

One sensible choice is to leave the first |Active| where it is, and
translate the second so its start time coincides with the end time of
the first:
\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams

dia = vcat' with {sep = 1}
      [ activeDR (-3) 1 red  <> tl
      , seqR
      , activeDR (-4) 3 blue <> tl
      , text' "="
      , vcat
        [ mconcat
          [ ( ((-4) & 0)  ~~  (0.5 & 0) ) # dashing [0.2,0.2] 0
          , triangle 0.5 # rotateBy (-1/4) # alignR # translateX 1 # lw 0
          ]
          # lw 0.2 # lc blue # fc blue # opacity 0.5
        , result
        ]
      ]

result = (draw $ Active (C (-3), r, O 8)) <> tl  -- $
  where
    r = hcat [ activeRect (-3) 1 red, activeRect 1 8 blue ]
\end{diagram}
\end{center}
It is easy to verify that this operation is associative.  However, the
asymmetry is already a bit unsettling: another valid choice would be
to translate the first value and leave the second unchanged.  (Because
of infinite |Active| values these are essentially the only choices; if
we restricted to only finite |Active|s, however, there would be more,
such as always centering the resulting |Active| with respect to time
$0$, or placing the start time at $0$.)

Once again, the existence of multiple choices, with no clear best
choice, prompts us to take a step back. In this case, it points at a
deeper phenomenon, which comes into sharper focus when we consider
what the identity element for |seqR| (or, dually, |seqL|) might be.
Just for the sake of concrete examples, let us assume that we have
chosen the semantics for sequential composition illustrated above,
where the second value is translated so that it follows the first.

Clearly, the identity element should have duration $0$, \ie it should
be some |z :: Active C O t a| with $t_s = t_e = t_z$ for some absolute
time $t_z$ (ugh, another arbitrary choice!).  Note that |z|'s function
is undefined everywhere, since the interval $[t_z,t_z)$ is empty. We
can see that |a `seqR` z = a| for all |a :: Active l O t a|, since |z|
gets translated and placed after |a|, which has no effect.  However,
generally speaking |z `seqR` a /= a|. Instead, |z `seqR` a| consists
of a translated copy of |a| with its start time at $t_z$.  Clearly,
this problem is independent of the particular value chosen for $t_z$.

One way around this would be to simply add a new distinguished
element to serve as the identity for |seqR|.  Although that works, it
is unsatisfying, and in fact there is a better solution.

So far, the problems with sequential composition all center around
having to make some arbitrary choice of a point in time: with |seqR|
we had to arbitrarily choose how to position the result in time; we
also had to arbitrarily choose a time $t_z$ for |z|, but no matter
what time we choose |z| cannot be a left identity for |seqR|.  Indeed,
in some sense the \emph{reason} |z| is not a left identity for |seqR|
is \emph{because} it has an arbitrary position in time, which ends up
causing the other |Active| to be translated.  But what if |z|
\emph{had no} absolute time?  What if we didn't have to make this kind
of choice for the result of |seqR| either?

This turns out to be exactly the right idea.  |seqR| and |seqL| do not
naturally operate on |Active| directly, but rather on
\emph{equivalence classes} of |Active| values up to translation!  That
is, we introduce a translation operation |trans :: d -> Active l r t a
-> Active l r t a| which is the derived group action of durations on
|Active| values. We then define the relation \[ a_1 \sim a_2 \quad
\iff \quad \exists d.\ |trans d a1| = |a2|, \] that is, two |Active|
values are related if one is a shifted copy of the other.
\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams

dia = vcat' with {sep = 1}
  [ a1                <> tl
  , text' "~"
  , a1 # translateX 4 <> tl
  ]
\end{diagram}
\end{center}
It is not hard to show this is an equivalence, and we may therefore
form the set of equivalence classes of |Active| values under this
relation, and write $[a]$ for the class of values equivalent to $a$.
Intuitively, we may think of these classes as |Active| values whose
position on the timeline has been ``forgotten''; pictorially, we can
just represent them without a timeline at all:
\begin{center}
\begin{diagram}[width=200]
import ActiveDiagrams
dia = (a1 # centerXY) <> phantom tl
\end{diagram}
\end{center}
We may now define |seqR| on equivalence classes by |[a1] `seqR` [a2] =
[a1 `seqR` a2]| (where the second |seqR| is the one from before, which
translates |a2| to start after |a1|).  It is not hard to verify that
this |seqR| is well-defined, associative, and has |[z]| as an
identity---note that there is only \emph{one} equivalence class of
zero-duration, closed-open |Active| values, consisting precisely of
|z| for all possible choices of $t_z$.

In fact, what we were really doing all along when discussing
sequential composition was working with \emph{representatives} of
these equivalence classes---that's why we kept running into an
arbitrary choice of time; we were trying to pick some concrete
representative of an equivalence class.

\section{|XActive| and |FActive|}
\label{sec:xactive-factive}

Given the above discussion, we split |Active| into two types.
|XActive|\footnote{The |X| stands for e|X|plicit or ``|X| marks the
  spot''.} will play the same role as |Active| did;
|FActive|\footnote{The |F| stands for |F|ree.} will classify
equivalence classes of |XActive| values.  Of course, we cannot
work with equivalence classes directly; any |FActive| value will
simply contain a \emph{representative} of an equivalence class, that
is, an |XActive|.  But giving it a distinct type allows us to
construct an API that does not allow the user to observe the
particular representative in use.

The most important remaining issue is to discuss conversion between
|XActive| and |FActive|.  But first, we need to clean up one tiny
remaining problem, which will lead to one more small difference
bewteen |XActive| and |FActive|.

\subsection{Fixing parallel composition}
\label{sec:fix-par-comp}

The problem is that with our new |inf/C/O| type indices, we can no
longer give a sensible type to parallel composition.  For example,
suppose we want to take the parallel composition of two values of types
|Active C C t a| and |Active O C t a|.  What should be the type of the
result---|Active C C t a| or |Active O C t a|?  In fact, it depends on
which of the left endpoints comes later!
\begin{center}
\begin{diagram}[width=300]
import ActiveDiagrams

b1  = activeD' C C (-6) 3 [red]
b2  = activeD' O C (-1) 5 [blue]
b12 = activeD' O C (-1) 3 [red,blue]

bs :: Diagram Cairo R2
bs = cat' unitY with {sep = 0.5} [b12, b2, b1]

b1'  = activeD' C C (-6) 3 [red]
b2'  = activeD' O C (-8) 5 [blue]
b12' = activeD' C C (-6) 3 [red,blue]

bs' = cat' unitY with {sep = 0.5} [b12', b2', b1']

dia = hcat [ bs <> tl , strutX 3, bs' <> tl ]
\end{diagram}
\end{center}
So it seems we need a dependent type.  However, there is a way out: in
fact, the more refined closed/open information is needed only in order
to be able to do sequential composition of |FActive| values.  For
|XActive|, we can require endpoints to be only infinite or closed,
which gives us just enough leverage to write a non-dependent type for
parallel composition, namely
\begin{spec}
par  :: XActive l1 r1 t a -> XActive l2 r2 t a
     -> XActive (Isect l1 l2) (Isect r1 r2) t a
\end{spec}
where |Isect| is defined by
\begin{spec}
Isect  inf  inf  =  inf
Isect  _    _    =  C
\end{spec}
The original |Monoid| and |Applicative| instances can be recovered for
a variant of |XActive| which existentially hides the |l| and |r| type
indices.

\subsection{Conversion}
\label{sec:conversion}

Converting from |XActive| to |FActive| is easy: we just wrap up the
|XActive|, ``forgetting'' its absolute location.  Converting in the
other direction, however, is tricky.  We have to specify how to pick a
particular representative from an equivalence class. One's first
instinct might be to have a function with the type
\begin{spec}
f2x :: t -> FActive l r t a -> XActive l r t a
\end{spec}
(with |l| and |r| somehow suitably restricted to only |inf| or |C|).
That is, to convert an |FActive| to |XActive| one needs only to
specify an absolute time.  However, this does not work!  The problem
is that |f2x| has no idea how the given time is supposed to relate to
the |FActive|.  If our |FActive| values were all finite, or even all
finite on the left, we could specify that the |FActive| should be
positioned with its start at the given time.  However, this completely
falls apart for bi-infinite |FActive| values.

The proposed solution is to store along with each |FActive| (and with
each |XActive|, while we're at it) a set of named ``anchor times''.
Some anchor times will always implicitly be available, for example,
``start'', ``end'', and ``center'' for finite intervals.  Some
operations can create new named anchor points; for example, sequential
composition may create one at the transition point.  The user can also
explicitly create named anchors (directly by specifying a time, in the
case of |XActive|, or relative to other existing anchors in the case
of |FActive|).  In order to convert from |FActive| to |XActive|, one
must specify a pair of a time \emph{and an anchor}; the |FActive| will
be positioned so the anchor is at the specified time.

\section{Related work}
\label{sec:related}

\todo{Hudak temporal media~\citep{hudak2004algebraic}: only considers the
equivalent of |FActive| (everything has a duration but no absolute
time).  Also restricts everything to be finite so the start and end
points can be used as alignment anchors, and allows parallel
composition only on values with the same duration.  So in order to do
parallel composition of unaligned values, or values of different
durations, one must first pad by the proper amount of space.  In
addition to being tedious, this means it cannot extend to infinite
values (since alignment of infinite values cannot be accomplished by
padding).  Also, does not address what happens at transition points.
Very different starting point---leaves primitives entirely abstract;
we are using |t -> a| where TM would use just |a|.  Wonder how much of
the algebraic approach carries over.}

\todo{FRAN}

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

\bibliographystyle{abbrvnat}
\bibliography{active-semantics}

\end{document}
