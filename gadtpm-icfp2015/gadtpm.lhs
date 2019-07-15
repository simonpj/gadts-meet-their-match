% -*- mode: LaTeX -*-
\documentclass{sigplanconf}
%include lhs2TeX.fmt 
%include lhs2TeX.sty

%-----------------------------------------------------------------------------
%
%               Template for sigplanconf LaTeX Class
%
% Name:         sigplanconf-template.tex
%
% Purpose:      A template for sigplanconf.cls, which is a LaTeX 2e class
%               file for SIGPLAN conference proceedings.
%
% Guide:        Refer to "Author's Guide to the ACM SIGPLAN Class,"
%               sigplanconf-guide.pdf
%
% Author:       Paul C. Anagnostopoulos
%               Windfall Software
%               978 371-2316
%               paul@windfall.com
%
% Created:      15 February 2005
%
%-----------------------------------------------------------------------------

% The following \documentclass options may be useful:

% preprint      Remove this option only once the paper is in final form.
% 10pt          To set in 10-point type instead of 9-point.
% 11pt          To set in 11-point type instead of 9-point.
% authoryear    To obtain author/year citation style instead of numeric.

\usepackage{amsmath}


%%%%%%%
%\usepackage{graphicx}
\usepackage{mathtools} % loads amsmath too  % for matrices
\usepackage{hhline}    % for custom lines in matrices
\usepackage{verbatim}  % for multiline comments
\usepackage{amssymb}   % for beautiful empty set
\usepackage{paralist}  % For inlined lists

\usepackage{prooftree} % For derivation trees

\usepackage[table]{xcolor} % for highlight
\usepackage{pgf}
\usepackage[T1]{fontenc}   % for textsc in headings

% For strange matrices
\usepackage{array}
\usepackage{multirow}
\usepackage{multicol}

\usepackage{xspace} % We need this for OutsideIn(X)X
%%%%%%%

\usepackage{float}
\floatstyle{boxed}
\restylefloat{figure}
\usepackage[all,cmtip]{xy}

% To balance the last page
\usepackage{flushend}

% Theorems
\usepackage{amsthm}
\newtheorem{theorem}{Theorem}

\usepackage{hyperref}

\input{macros}

% Wildcards
\newcommand\WILD{\mbox{@_@}}

\usepackage[labelfont=bf]{caption}

\usepackage{mathrsfs}

\clubpenalty = 10000
\widowpenalty = 10000
\displaywidowpenalty = 10000

% Tables should have the caption above
\floatstyle{plaintop}
\restylefloat{table}
% \usepackage{caption}
% \DeclareCaptionFormat{myformat}{#1#2#3\hrulefill}
% \captionsetup[table]{format=myformat}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{ICFP'15}{August 31 -- September 2, 2015, Vancouver, BC, Canada}
\CopyrightYear{2015}
\crdata{978-1-4503-3669-7/15/08}

%% \conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country} 
%% \copyrightyear{20yy} 
%% \copyrightdata{978-1-nnnn-nnnn-n/yy/mm} 
\doi{nnnnnnn.nnnnnnn}

% Uncomment one of the following two, if you are not going for the 
% traditional copyright transfer agreement.

%\exclusivelicense                % ACM gets exclusive license to publish, 
                                  % you retain copyright

%\permissiontopublish             % ACM gets nonexclusive license to publish
                                  % (paid open-access papers, 
                                  % short abstracts)

%\titlebanner{Draft}                           % These are ignored unless
\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{GADTs Meet Their Match:}
\subtitle{Pattern-Matching Warnings That Account for GADTs, Guards, and Laziness}
%% \title{GADTs meet their match}
%% \subtitle{Pattern-matching warnings that account for GADTs, guards, and laziness.}

\authorinfo{Georgios Karachalias}
           {Ghent University, Belgium}
           {georgios.karachalias@@ugent.be}
\authorinfo{Tom Schrijvers}
           {KU Leuven, Belgium}
           {tom.schrijvers@@cs.kuleuven.be}
\authorinfo{Dimitrios Vytiniotis \\ Simon Peyton Jones}
           {Microsoft Research Cambridge, UK}
           {\{dimitris,simonpj\}@@microsoft.com}

\maketitle

\begin{abstract}
% GADT (typing) problem
For ML and Haskell, accurate warnings when a function definition has redundant or
missing patterns are mission critical.  But today's compilers
generate bogus warnings when the programmer uses guards (even simple ones),
GADTs, pattern guards, or view patterns.  We give the first algorithm
that handles all these cases in a single, uniform framework, together
with an implementation in GHC, and evidence of its utility in practice.
\end{abstract}

\category{D.3.2}{Language Classifications}{Applicative (functional) languages}
\category{D.3.3}{Language Constructs and Features}{Patterns}

% general terms are not compulsory anymore, 
% you may leave them out
% \terms
% term1, term2

\keywords
Haskell, pattern matching, Generalized Algebraic Data Types, \OutsideIn{X}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Section 1 (Introduction)
\section{Introduction}\label{introduction}

Is this function (in Haskell) fully defined?

> zip :: [a] -> [b] -> [(a,b)]
> zip []     []     = []
> zip (a:as) (b:bs) = (a,b) : zip as bs

No, it is not: the call @(zip [] [True])@ will fail, because neither
equation matches the call.  Good compilers will report missing
patterns, to warn the programmer that the function is only partially
defined.  They will also warn about completely-overlapped, and hence
redundant, equations.  Although technically optional for soundness,
these warnings are incredibly useful in practice, especially when the
program is refactored (i.e. throughout its active life), with
constructors added and removed from the data type
(Section~\ref{sec:challenge}).

But what about this function?

> vzip :: Vect n a -> Vect n b -> Vect n (a,b)
> vzip VN        VN        = VN
> vzip (VC x xs) (VC y ys) = VC (x,y) (vzip xs ys)

where the type @Vect n a@ represents lists of length @n@ with element type @a@.
@Vect@ is a Generalised Algebraic Data Type (GADT):

> data Vect :: Nat -> * -> * where
>   VN :: Vect Zero a
>   VC :: a -> Vect n a -> Vect (Succ n) a

Unlike @zip@, function @vzip@ is \emph{fully} defined: a call with arguments of unequal length,
such as @(vzip VN (VC True VN))@, is simply ill-typed.  Comparing @zip@ and @vzip@,
it should be clear that only a \emph{type-aware} algorithm can correctly decide
whether or not the pattern-matches of a function definition are exhaustive.

Despite the runaway popularity of GADTs, and other pattern-matching
features such as
view patterns and pattern guards,
no production compiler known to us gives accurate pattern-match
overlap and exhaustiveness warnings when these features are used.
Certainly our own compiler, GHC, does not; and nor does OCaml.
In this paper we solve the problem. Our contributions are these:
\begin{itemize}
\item We characterise the challenges of generating accurate warnings in Haskell (Section~\ref{sec:challenge}).
The problem goes beyond GADTs!  There are subtle issues concerning nested patterns,
view patterns, guards, and laziness;
the latter at least has never even been noticed before.

\item We give a type-aware
algorithm for determining missing or redundant patterns (Sections~\ref{sec:general-overview} and~\ref{sec:algorithm}).
The algorithm is parameterised over an oracle that can solve constraints: both type
constraints and boolean constraints for guards. Extending the oracle allows us to accommodate type
system extensions or improve the precision of the reported warnings {\em without} affecting the main
algorithm at all.

The central abstraction in this algorithm is the compact symbolic representation of a set of values by a triple 
$(\vtup{\Gamma}{u}{\Delta})$ consisting of an environment $\Gamma$, a syntactic value abstraction $u$ and a 
constraint $\Delta$ (Section~\ref{sec:syntax}). The key innovation is to include the constraints $\Delta$ to refine the set of values; for example $(\vtup{x{:}@Int@}{@Just@\;x}{x @>@ 3})$ is the set of all applications of @Just@ to integers bigger than $3$.
This allows us to handle GADTs, guards and laziness uniformly.

\item We formalise the correctness of our algorithm
  (Section~\ref{sec:semantics}) with respect to the Haskell semantics of
  pattern matching.

\item We have implemented our algorithm in GHC, a production quality
  compiler for Haskell (Section~\ref{s:implementation}). The new
  implementation is of similar code size as its predecessor although 
  it is much more capable. It reuses GHC's existing type constraint solver as an
  oracle.

\item We demonstrate the effectiveness of the new checker on a set of
  actual Haskell programs submitted by GHC users, for whom inaccurate
  warnings were troublesome (Section~\ref{sec:evaluation}).




\end{itemize}
There is quite a bit of related work, which we discuss in Section~\ref{sec:related}.

% \newpage
%===============================================================================
% Section 2 (Overview)
\section{The Challenges That We Tackle} \label{sec:challenge}

The question of determining exhaustiveness and redundancy of pattern matching
has been well studied (Section~\ref{sec:related}), but almost exclusively
in the context of purely structural matching. In this section we identify three
new challenges:
\begin{itemize}
\item The challenge of GADTs and, more generally,
of patterns that bind arbitrary existential type variables and constraints (Section~\ref{sec:challenge-gadts}).
\item The challenge of laziness (Section~\ref{sec:challenge-laziness}).
\item The challenge of guards (Section~\ref{sec:challenge-guards}).
\end{itemize}
These issues are all addressed individually in the literature but, to
our knowledge, we are the first to tackle all three in a single unified framework,
and implement the unified algorithm in a production compiler.

%-------------------------------------------------------------------------------
\subsection{Background}

Given a function definition (or case expression) that uses pattern matching,
the task is to determine whether any clauses are missing or redundant.
\begin{description}
\item[Missing clauses.]
Pattern matching of a sequence of clauses
is \emph{exhaustive} if every well-typed argument vector matches one
of the clauses.  For example:
\begin{code}
zip []     []     = []
zip (a:as) (b:bs) = (a,b) : zip as bs
\end{code}
@zip@ is not exhaustive because there is a well-typed call that does
not match any of its clauses; for example @zip [] [True]@.
So the clause @zip [] (b:bs) = e@ is \emph{missing}.
\item[Redundant clauses.]  If there is no well-typed value that matches
the left hand side of a clause, the right hand side of the clause can never be
accessed and the clause is \emph{redundant}.  For example, this equation would be redundant:
\begin{code}
vzip VN (VCons x xs) = ....
\end{code}
\end{description}
\noindent
Since the application of a partial function to a value outside its domain results
in a runtime error, the presence of non-exhaustive pattern matches often
indicates a programmer error. Similarly, having redundant clauses in a match is
almost never intentional and indicates a programmer error as well. Fortunately,
this is a well-studied problem\cite{augustsson:compiling-pm,
wadler:compiling-pm,
maranget:warnings,maranget:lazy-pm,maranget:optimising,
thiemann:repeated-tests}:
compilers can detect and warn programmers about these anomalies.
We discuss this related work in
Section~\ref{sec:related}.

However, Haskell has moved well beyond simple constructor patterns: it has
overloaded literal patterns, guards, view patterns, pattern synonyms, and
GADTs. In the rest of
this section we describe these new challenges, while in subsequent sections
we show how to address them.

%-------------------------------------------------------------------------------
\subsection{The Challenge of GADTs}\label{sec:challenge-gadts}

In recent years, Generalized Algebraic Data Types (GADTs, also known as guarded
recursive data types~\cite{recdatac}, first-class phantom types~\cite{phantom},
etc.) have appeared in many programming languages, including Haskell
\cite{unigadts,outsidein}, OCaml~\cite{ocamlgadts} and $\Omega$mega~\cite{omega}. Apart
from the well-studied difficulties they pose for type inference, GADTs
also introduce a qualitatively-new
element to the task of determining missing or redundant patterns.
As we showed in the Introduction, only a \emph{type-aware} algorithm can
generate accurate warnings.

Indeed, although GADTs have been supported by the {\em Glasgow Haskell
Compiler} (GHC) since March 2006~\cite{unigadts}, the pattern match check was
never extended to take account of GADTs, resulting in many user bug reports.
Although there have been attempts to
improve the algorithm (see tickets\footnote{Tickets are GHC bug reports,
recorded through the project's bug/issue tracking system:
\url{ghc.haskell.org/trac/ghc}.} \ticket{366} and \ticket{2006}), all of them
are essentially {\em ad-hoc} and handle only specific cases.

This matters.  GHC warns (wrongly) about missing patterns in the
definition of @vzip@.  Programmers often try to suppress the warning by adding
a third fall-through clause:

> vzip _ _ = error "Inaccessible branch"

That suppresses the warning but at a terrible cost: if you modify the
data type (by adding a constructor, say), you would hope that you
would get warnings about missing cases in @vzip@.  But no, the
fall-through clause covers the new constructors, so GHC stays silent.
At a stroke, that obliterates one of the primary benefits warnings for missing
and redundant clauses: namely, their support during software maintenance and
refactoring, perhaps years after the original code was written.

Moreover, GADTs are special case of something more general:
\emph{data constructors that bind arbitrary
existential type variables and constraints}.  For example:
\begin{code}
data T a where
  MkT :: (C a b, F a ~ G b) => a -> b -> T a
\end{code}
where @C@ is a type class and @F@ and @G@ are type functions.
Here the constructor @MkT@ captures an existential type variable @b@,
and binds the constraints @(C a b, F a ~ G b)@.
In the rest of the paper we draw examples from GADTs, but our formalism and
algorithm handles the general case.

%-------------------------------------------------------------------------------
\subsection{The Challenge of Laziness}\label{sec:challenge-laziness}

Haskell is a lazy language, and it turns out that laziness interacts in an
unexpectedly subtle way with pattern matching checks.
Here is an example, involving two GADTs:

> data F a where      data G a where
>   F1 :: F Int         G1 :: G Int
>   F2 :: F Bool        G2 :: G Char
>
> h :: F a -> G a -> Int
> h F1 G1 = 1
> h _  _  = 2

Given @h@'s type signature, its only well-typed non-bottom arguments
are @F1@ and @G1@ respectively. So, is the second clause for @h@
redundant?  No!  Consider the call $@(h F2@\,\bot@)@$, where
$\bot$ is a diverging value, or an error value such as @(error "urk")@.
Pattern matching in Haskell works top-to-bottom, and left-to-right.
So we try the first equation, and match the pattern @F1@ against the argument @F2@.
The match fails, so we fall through to the second equation, which succeeds, returning @2@.

Nor is this subtlety restricted to GADTs.  Consider:

> g :: Bool -> Bool -> Int
> g _    False = 1
> g True False = 2
> g _    _     = 3

Is the second equation redundant?
It certainly \emph{looks} redundant: if the second clause matches
then the first clause would have matched too, so @g@ cannot possibly
return @2@.  The right-hand side of the second clause is certainly dead code.

Surprisingly, though, \emph{it is not correct to remove the second equation}.
What does the call @(g@\,$\bot$\,@True)@ evaluate to, where $\bot$ is a looping value?
Answer: the first clause fails to match, so we attempt to match the second.
That requires us to evaluate the first argument of the call, $\bot$, which will
loop.  But if we omitted the second clause, @(g@\,$\bot$\,@True)@ 
would return @3@.

In short, even though the right-hand side of the second equation is dead code,
the equation cannot be removed without (slightly) changing the semantics of the
program.  So far as we know, this observation has not been made before, although
previous work~\cite{maranget:warnings} would quite sensibly classify the second equation as
non-redundant (Section~\ref{sec:related}). 

The same kind of thing happens with GADTs.  With the same definitions for @F@ and @G@,
consider

> k :: F a -> G a -> Int
> k F1 G1 = 1
> k _  G1 = 2

Is the second equation redundant?  After all, anything that matches it
would certainly have matched the first equation (or caused divergence if the
first argument was $\bot$).  So the RHS is definitely dead code; @k@ cannot
possibly return @2@.  But removing the second clause would make the definition
of @k@ inexhaustive: consider the call $@(k F2@\,\bot@)@$.

The bottom line is this: if we want to report accurate warnings, we must
take laziness into account. We address this challenge in this
paper.

%-------------------------------------------------------------------------------
\subsection{The Challenge of Guards} \label{sec:challenge-guards}

Consider this function:

> abs1 :: Int -> Int
> abs1 x | x < 0     = -x
>        | otherwise = x

This function makes use of Haskell's boolean-valued \emph{guards}, introduced by ``@|@''.
If the guard returns @True@, the clause succeeds and the right-hand side is evaluated;
otherwise pattern-matching continues with the next clause. 

It is clear to the reader that this function is exhaustive, but not so clear
to a compiler.
Notably, @otherwise@ is not a keyword; it is simply a value defined by @otherwise = True@.
The compiler needs to know that fact to prove that the pattern-matching is exhaustive.
What about this version:

> abs2 :: Int -> Int
> abs2 x | x < 0  = -x
>        | x >= 0 = x

Here the exhaustiveness of pattern-matching depends on knowledge of the properties of
@<@ and @>=@.  In general, the exhaustiveness for pattern matches involving guards
is clearly undecidable; for example, it could depend on a deep theorem of
arithmetic.  But we would like the compiler to do a good job in common cases
such as @abs1@, and perhaps @abs2@.

GHC extends guards further with \emph{pattern guards}.  For example:

> append xs ys
>   | []     <- xs = ys
>   | (p:ps) <- xs = p : append ps ys

The pattern guard matches a specified expression (here @xs@ in both cases) against
a pattern; if matching succeeds, the guard succeeds, otherwise pattern matching
drops through to the next clause.
Other related extensions to basic pattern matching include literal patterns and
\emph{view patterns}~\cite{views,transformational}.

All these guard-like extensions pose a challenge to determining
the exhaustiveness and redundancy of pattern-matching, because pattern matching
is no longer purely structural.  Every real compiler must grapple with this issue,
but no published work gives a systematic account of how to do so.  We do so here.

%===============================================================================
\section{Overview of Our Approach}\label{sec:general-overview}

\begin{figure}[t]
\centering
\pgfimage[width=0.8\columnwidth]{images/patmatchalg.pdf}
\caption{Algorithm Outline}
\label{fig:algorithm_outline}
\end{figure}

In this section we describe our approach in intuitive terms,
showing how it addresses each of the three challenges of Section~\ref{sec:challenge}.
We subsequently formalise the algorithm in Section~\ref{sec:formal}.

%-------------------------------------------------------------------------------
\subsection{Algorithm Outline} \label{sec:outline}

The most common use of pattern matching in Haskell is when
a function is defined using multiple \emph{clauses}:
$$
\begin{array}{l@@{\hspace{1mm}}l@@{}l@@{}l@@{\hspace{1mm}}c@@{\hspace{1mm}}l@@{\hspace{4mm}}l}
f & p_{11} & \ldots & p_{1n} & = & e_1 & \text{Clause 1}\\
\multicolumn{4}{c}{\ldots} \\
f & p_{m1} & \ldots & p_{mn} & = & e_m & \text{Clause $m$} 
\end{array}
$$
From the point of view of pattern matching, the function name ``$f$''
is incidental: all pattern matching in Haskell can be regarded as a
sequence of clauses, each clause comprising a pattern vector and a right hand side.  
For example, a @case@ expression also has multiple clauses (each with only
one pattern); a Haskell pattern matching lambda has a single clause
(perhaps with multiple patterns); and so on.

In Haskell, pattern matching on a sequence of clauses is carried out top-to-bottom, and
left-to-right. In our function $f$ above, Haskell matches the first argument against $p_{11}$,
the second against $p_{12}$ and so on.  If all $n$ patterns in the first clause match,
the right hand side is chosen; if not, matching resumes with the next clause.
Our algorithm, illustrated in Figure~\ref{fig:algorithm_outline}, works in the same way: it
analyses the clauses one by one, from top to bottom. The analysis $\mathit{patVectProc}$ of an
individual clause takes a compact symbolic representation of the vector of argument values that are
possibly submitted to the clause, and partitions these values into three different groups:
\begin{description}
\item[$\setcovered{}$] The values that are \emph{covered} by the clause; that is, values
that match the clause without divergence, so that the right-hand side is
evaluated.
\item[$\setdiverges{}$] The values that \emph{diverge} when matched against the clause,
so that the right-hand side is not evaluated,
but neither are any subsequent clauses matched.
\item[$\setuncovered{}$] The remaining \emph{uncovered} values; that is, the values that fail to match
the clause, without divergence.
\end{description}
\noindent As illustrated in Figure~\ref{fig:algorithm_outline}, the input to the
first clause represents all possible values, and each subsequent clause is
fed the uncovered values of the preceding clause.  
For example, consider the function @zip@ from the Introduction:

> zip []     []     = []
> zip (a:as) (b:bs) = (a,b) : zip as bs

We start the algorithm with $\setcovered{0} = \{@_ _@$\}, where we use ``@_@'' to 
stand for ``all values''. Processing the first clause gives:
$$
\begin{array}{rcl}
\setcovered{1}   & = & \{ @[] []@ \} \\
\setdiverges{1}  & = & \{ \bot\,@_@,\; @[]@\,\bot \} \\
\setuncovered{1} & = & \{ @[] (_:_)@,\; @(_:_) _@ \} \\
\end{array}
$$
The values that fail to match the first clause, and do so without divergence,
are $U_1$, and these values are fed to the second clause.  Again we
divide the values into three groups:
$$
\begin{array}{rcl}
\setcovered{2}   & = & \{  @(_:_) (_:_)@ \} \\
\setdiverges{2}  & = & \{ @(_:_)@\,\bot \} \\
\setuncovered{2} & = & \{ @[] (_:_)@,\; @(_:_) []@ \}
\end{array}
$$
Now, $\setuncovered{2}$ describes the values that fail to match either clause. Since it is
non-empty, the clauses are not exhaustive, and a warning should be generated.
In general we generate three kinds of warnings:
\begin{enumerate}
\item If the function is defined by $m$ clauses, and $\setuncovered{m}$ is non-empty, then
the clauses are non-exhaustive, and a warning should be reported.  It is usually
helpful to include the set $\setuncovered{m}$ in the error message, so that the user can see
which patterns are not covered.
\item Any clause $i$ for which $\setcovered{i}$ and $\setdiverges{i}$ are both empty is redundant, and
can be removed altogether.
\item Any clause $i$ for which $\setcovered{i}$ is empty, but $\setdiverges{i}$ is not, has an
inaccessible right hand side even though the equation cannot be removed.
This is unusual, and deserves its own special kind of warning; again, including $\setdiverges{i}$ in
the error message is likely to be helpful.
\end{enumerate}

\noindent Each of $\setcovered{}, \setuncovered{}$, and $\setdiverges{}$ is a set of
\emph{value abstractions}, a compact representation of a set of value vectors
that are covered, uncovered, or diverge respectively.
For example, the value abstraction $@(_:_)@\; @[]@$ stands for value vectors
such as
\begin{code}
  (True:[])              []
  (False : (True : []))  []
\end{code}
and so on. Notice in $\setdiverges{1}, \setdiverges{2}$ that our value abstractions
must include $\bot$, so that we can describe values that cause matching to diverge.

\subsection{Handling Constraints} \label{sec:outline-gadt}

Next we discuss how these value abstractions may be extended to handle GADTs.
Recall @vzip@ from the Introduction

> vzip :: Vect n a -> Vect n b -> Vect n (a,b)
> vzip VN        VN        = VN
> vzip (VC x xs) (VC y ys) = VC (x,y) (vzip xs ys)

What do the uncovered sets $\setuncovered{i}$ look like?  Naively they would look like
that for @zip@:
$$
\begin{array}{rcl}
\setuncovered{1} & = & \{ @VN (VC _ _)@,\; @(VC _ _) _@ \} \\
\setuncovered{2} & = & \{ @VN (VC _ _)@,\; @(VC _ _) VN@ \}
\end{array}
$$
To account for GADTs we add \emph{type constraints} to our value abstractions, to give this:
$$
\begin{array}{rcl}
\setuncovered{1} & = & \{ @VN (VC _ _)@ \deltasep (@n@ \sim @Zero@,\, @n@ \sim @Succ n2@) \\
& & , \, @(VC _ _) _@ \; \deltasep (@n@ \sim @Succ n2@) \} 
\end{array}
$$
Each value tuple abstraction in the set now comes with a type equality constraint (e.g. $@n@ \sim @Succ n2@$),
and represents values of the specified syntactic shape, \emph{for which the equality constraint is
satisfiable} at least for some substitution of its free variables.
The first abstraction in $\setuncovered{1}$ has a constraint that is \emph{unsatisfiable}, 
because
@n@ cannot simultaneously be equal to both @Zero@ and @Succ n2@.  Hence the first
abstraction in $\setuncovered{1}$ represents the empty set of values and can be discarded.
Discarding it, and processing the second clause gives
$$
\begin{array}{rcl}
\setuncovered{2} & = & \{ @(VC _ _) VN@ \deltasep (@a@ \sim @Succ n@,\, @a@ \sim @Zero@) \}
\end{array}
$$
\noindent Again the constraint is unsatisfiable, so $\setuncovered{2}$ is empty, which
says that the function is exhaustive.

We have been a bit sloppy with binders (e.g. where is @n2@ bound?), but we will
tighten that up in the next section.  The key intuition is this: \emph{the abstraction 
$u \deltasep \Delta$ represents the set of values whose syntactic shape is given by $u$,
and for which the type constraint $\Delta$ is satisfied}.

\subsection{Guards and Oracles}

In the previous section we extended value abstractions with a conjunction of
type-equality constraints.  It is straightforward to take the idea further, and
add term-equality constraints.  Then the final uncovered set for function @abs2@
(Section~\ref{sec:challenge-guards}) might look like this:
$$
\begin{array}{rcl}
\setuncovered{2} & = & \{ @x@ \deltasep (@False@ = @x<0@,\, @False@ = @x>=0@) \}
\end{array}
$$
We give the details of how we generate this set in Section~\ref{sec:formal},
but intuitively the reasoning goes like this: if neither clause for @abs2@ matches,
then both boolean guards must evaluate to @False@.
Now, if the compiler knows enough about arithmetic, it may be able to determine that the
constraint is unsatisfiable, and hence that $\setuncovered{2}$ is empty, and
hence that @abs2@ is exhaustive.

For both GADTs and guards, the question becomes this: \emph{is the constraint $\Delta$
unsatisfiable?}  And that is a question that has been \emph{extremely} well studied,
for many particular domains.  For the purposes of this paper, therefore, we treat 
satisfiability as a black box, or oracle: the algorithm is parameterised
over the choice of oracle.  For type-equality constraints we have
a very good oracle, namely GHC's own type-constraint solver.  For term-level constraints we
can plug in a variety of solvers.  This modular separation of concerns is extremely helpful,
and is a key contribution of our approach.

\subsection{Complexity}\label{sec:complexity}

Every pattern-checking algorithm has terrible worst-case complexity,
and ours is no exception.  For example, consider

> data T = A | B | C
> f A A = True
> f B B = True
> f C C = True

What values $\setuncovered{3}$ are not covered by @f@? Answer

> { A B, A C, B A, B C, C A, C B }

The size of the uncovered set is the square of the number of constructors in @T@.
It gets worse: Sekar et al.~\cite{Sekar:1992:APM} show that the
problem of finding redundant clauses is NP-complete, by encoding the boolean
satisfiability (SAT) problem into it. 
So the worst-case running time is necessarily exponential.  But so is
Hindley-Milner type inference!  As with type inference, we hope that
worst case behaviour is rare in practice.  Moreover, GHC's current
redundancy checker suffers from the same problem without obvious
problems in practice. We have gathered quantitative data about set sizes to
better characterise the problem, which we discuss in Appendix~\ref{pm:performance}.

%===============================================================================
\section{Our Algorithm in Detail} \label{sec:formal} \label{sec:algorithm}

%-------------------------------------------------------------------------------


\begin{figure}[t]
\centering
\[
  \begin{array}{l@@{\hspace{1mm}}l@@{\hspace{8pt}}l}
     \multicolumn{3}{l}{\textbf{Types}} \\
     \tau & ::= a \mid \tau_1 \rightarrow \tau_2 \mid T\:\overline{\tau} \mid \dots & \text{Monotypes} \\
     \multicolumn{2}{l}{a, b, a', b', \dots}                          & \text{Type variables} \\
     T &                                                              & \text{Type constructors} \\
     \Gamma & ::= \epsilon \mid \Gamma, a \mid \Gamma, x : \tau  & \text{Typing environment} \\[2mm]
     \multicolumn{3}{l}{\textbf{Terms and clauses}} \\
     \multicolumn{2}{l}{f,g,x,y,\dots}        & \text{Term variables} \\
     e &                                      & \text{Expression} \\
     c & ::= \vec{p} \, \rightarrow \, e      & \text{Clause} \\[2mm]
     \multicolumn{3}{l}{\textbf{Patterns}} \\
     K &                                      & \text{Data constructors} \\
     p,q & ::= x \mid K\: \vec{p} \mid G      & \text{Pattern} \\
     G & ::= p \leftarrow e                 & \text{Guard} \\[2mm]
     \multicolumn{3}{l}{\textbf{Value abstractions}} \\
     S,C,U,D & ::= \overline{v}             & \text{Value set abstraction} \\
     v & ::= \vtup{\Gamma}{\vec{u}}{\Delta} & \text{Value vector abstraction} \\
     u,w & ::= x \mid K\: \vec{u}           & \text{Value abstraction} \\[2mm]
     \multicolumn{3}{l}{\textbf{Constraints}} \\
     \Delta & ::= \epsilon \mid \Delta\cup\Delta  \\
            & \hspace{3mm} \mid Q & \text{Type constraint} \\
            & \hspace{3mm} \mid x \termeq e        & \text{Term-equality constraint} \\
            & \hspace{3mm} \mid x \termeq \bot     & \text{Strictness constraint} \\
      Q  & ::= \tau \typeeq \tau  & \text{Type-equality constraint} \\
         & \hspace{3mm}  \mid ... & \text{other constraint}  \\
  \end{array}
\]
\caption{Syntax}
\label{fig:alg_syntax}
\end{figure}

% In this section we describe our algorithm in detail.

\subsection{Syntax} \label{sec:syntax}

Figure~\ref{fig:alg_syntax} gives the syntax used in the formalisation of the
algorithm. The syntax for types, type constraints and type environments is entirely
standard.  We are explicit about the binding of type variables in $\Gamma$, but
for this paper we assume they all have kind $*$, so we omit their kind ascriptions.  
(Our real implementation supports higher kinds, and indeed kind polymorphism.)

A \emph{clause} is a vector of patterns $\vec{p}$ and a right-hand
side $e$, which should be evaluated if the pattern matches.  Here, a
``vector'' $\vec{p}$ of patterns is an ordered sequence of patterns:
it is either empty, written $\emptyvec$, or is of the form $p\, \vec{p}$.

A pattern $p$ is either a variable pattern $x$, a constructor pattern
$K\: \vec{p}$ or a \emph{guard} $G$.  We defer everything concerning guards
to Section~\ref{sec:guards}, so that we can initially concentrate on GADTs.

Value abstractions play a central role in this paper, and stand for 
sets of values.  They come in three forms:
\begin{itemize}
\item A \emph{value set abstraction} $S$ is a set of value abstractions $\bar{v}$.
We use an overline $\bar{v}$ (rather than an arrow) 
to indicate that the order of items in $S$ does not matter.
\item A \emph{value vector abstraction} $v$ has the form $\vtup{\Gamma}{\vec{u}}{\Delta}$.
It consists of a vector $\vec{u}$ of
syntactic value abstractions, and a constraint $\Delta$.
The type environment $\Gamma$ binds the free variables of $\vec{u}$ and $\Delta$.
\item A \emph{syntactic value abstraction} $u$ is either a variable $x$, or is of the form $K\,\vec{u}$, where
$K$ is a data constructor.
\end{itemize}
A value abstraction represents a set of values, using the intuitions
of Sections~\ref{sec:outline} and \ref{sec:outline-gadt}.  We formalise these sets precisely in
Section~\ref{sec:semantics}.

Finally, a constraint $\Delta$ is a conjunction of either type constraints $Q$ or term equality
constraints $x \termeq e$, and in addition {\em strictness} constraints $x\termeq\bot$. Strictness
constraints are important for computing diverge sets for which we've used informal notation in the
previous sections: For example $\{ @(_:_)@\,\bot \}$ is formally represented 
as $\{\vtup{\Gamma}{(x@:@y)~z}{z\termeq\bot} \}$ for some appropriate environment $\Gamma$.

Type constraints include type equalities $\tau_1 \typeeq \tau_2$ but
can also potentially include other constraints introduced by pattern matching or type signatures
(examples would be type class constraints or refinements~\cite{liquid,liquidhaskell}). We 
leave the syntax of $Q$ deliberately open. 

%-------------------------------------------------------------------------------
\subsection{Clause Processing}\label{s:formalisation:core}

\begin{figure*}\small
\centering

\[ \ruleform{ \mathit{patVectProc}(\ps, S) = \triple{\SC}{\SU}{\SB} } \]
\[
\begin{array}{c}
  \mathit{patVectProc}\: (\ps, S) = \triple{\SC}{\SU}{\SB}
  ~~~~ \text{where}
  ~~~~ \begin{array}{l@@{\hspace{0.5mm}}c@@{\hspace{0.5mm}}l@@{\hspace{0.5mm}}l@@{\hspace{1mm}}l@@{\hspace{1mm}}l}
       \SC & = & \{ w & \mid v \in S, w & \in \ucovered{\ps}{v}, & \vdash_\textsc{Sat} w  \} \\
       \SU & = & \{ w & \mid v \in S, w & \in \uuncovered{\ps}{v},         & \vdash_\textsc{Sat} w  \} \\
       \SB & = & \{ w & \mid v \in S, w & \in \ueliminated{\ps}{v}, & \vdash_\textsc{Sat} w  \} \\
       \end{array}
\end{array}
\]

% ------------------------------ Covered ----------------------------------
\[\arraycolsep=1.4pt
\begin{array}{llllllll}
\multicolumn{7}{c}{\ruleform{ \ucovered{\ps}{v} = \SC \;\; \text{(always empty or singleton set)}}} \\[2mm]

\rulename{CNil}\quad &
  \COVERED & \emptyvec & (\vtup{\Gamma}{\emptyvec}{\Delta}) & = & 
        \{~\vtup{\Gamma}{\emptyvec}{\Delta}~\} \\

\rulename{CConCon} ~~~~ & 
  \COVERED & {((\cons{K_i}{\vec{p}})\:\vec{q})} & ({\vtup{\Gamma}{(\cons{K_j}{\vec{u}})\:\vec{w}}{\Delta}}) & = &
  \left\{\begin{array}{l@@{\hspace{2mm}}l}
        \MAP~(\ZIPCON\: K_i)~(\covered{\vec{p}\:\vec{q}}{\vtup{\Gamma}{\vec{u}\:\vec{w}}{\Delta}})
           & \text{if } K_i = K_j \\
        \varnothing      
           & \text{if } K_i \neq K_j 
  \end{array}\right. \\

\rulename{CConVar}\quad & 
  \COVERED & ({(\cons{K_i}{\vec{p}})\:\vec{q}}) & ({\vtup{\Gamma}{x\:\vec{u}}{\Delta}}) & = &
    \covered{(\cons{K_i}{\vec{p}})\:\vec{q}}{\vtup{\Gamma'}{(\cons{K_i}{\YS{}})\:\vec{u}}{\Delta'}} \\
   & &&  & & \hspace{-6pt} \begin{array}{ll}
            \text{where} & \YS{} \# \Gamma \quad \as \# \Gamma \quad (x{:}\tau_x) \in \Gamma 
                         \quad K_i :: \forall \as. Q \Rightarrow \vec{\tau} \rightarrow \tau \\
                         & \Gamma' = \Gamma,\as, \vec{y}{:}\vec{\tau} \\
                         & \Delta' = \Delta \cup Q \cup \tau \sim \tau_x \cup x \termeq \cons{K_i}{\YS{}} 
           \end{array} \\

\rulename{CVar}\quad  & 
  \COVERED & (x\:\vec{p}) & ({\vtup{\Gamma}{u\:\vec{u}}{\Delta}}) & = &
   \MAP\: (\CONS\: u)\: (\covered{\vec{p}}{\vtup{\Gamma, x{:}\tau}{\vec{u}}{\Delta \cup x \termeq u}}) 
   & \text{where}\; x \# \Gamma \hspace{2mm} \Gamma \vdash u : \tau  \\

\rulename{CGuard} & 
  \COVERED & {((p\leftarrow e)\:\vec{p})} & ({\vtup{\Gamma}{\vec{u}}{\Delta}}) & = &
     \MAP~\TAIL~(\covered{p\:\vec{p}}{\vtup{\Gamma,y{:}\tau}{y~\vec{u}}{\Delta \cup y \termeq e}})
  & \text{where}\; y \# \Gamma \hspace{2mm} \Gamma \vdash e : \tau  \\[4mm]

% ------------------------------ Uncovered ----------------------------------
\multicolumn{7}{c}{\ruleform{ \uuncovered{\ps}{v} = \SU}} \\[2mm]

\rulename{UNil}    & 
  \UNCOVERED & \emptyvec & (\vtup{\Gamma}{\emptyvec}{\Delta}) & = & \varnothing \\

\rulename{UConCon} ~~~~ & 
  \UNCOVERED & ({(K_i\:\vec{p})\:\vec{q}}) & ({\vtup{\Gamma}{(K_j\:\vec{u})\:\vec{w}}{\Delta}}) & = & 
  \left\{\begin{array}{l@@{\hspace{2mm}}l}
        \MAP~(\ZIPCON\: K_i)~(\uncovered{\vec{p}\:\vec{q}}{\vtup{\Gamma}{\vec{u}\:\vec{w}}{\Delta}} 
           & \text{if } K_i = K_j \\
        \{\:\vtup{\Gamma}{(K_j\:\vec{u})\:\vec{w}}{\Delta}\:\}
           & \text{if } K_i \neq K_j
  \end{array}\right. \\

\rulename{UConVar}    & 
  \UNCOVERED & ({(K_i\:\vec{p})\:\vec{q}}) & ({\vtup{\Gamma}{x\:\vec{u}}{\Delta}}) & = & 
    \bigcup_{K_j} \uncovered{(\cons{K_i}{\vec{p}})\:\vec{q}}{\vtup{\Gamma'}{(\cons{K_j}{\YS{}})\:\vec{u}}{\Delta'}} \\
  & &&  & & \hspace{-6pt} \begin{array}{ll}
          \text{where} & \YS{} \# \Gamma \quad \as \# \Gamma \quad (x{:}\tau_x) \in \Gamma \quad
                       K_j :: \forall\as. Q \Rightarrow \vec{\tau} \rightarrow \tau \\
                       & \Gamma' = \Gamma,\as,\vec{y}{:}\vec{\tau} \quad
                         \Delta' = \Delta \cup Q \cup \tau \sim \tau_x \cup x \termeq \cons{K_j}{\YS{}}
         \end{array}
\\
\rulename{UVar}    & 
  \UNCOVERED & ({x\:\vec{p}}) & ({\vtup{\Gamma}{u\:\vec{u}}{\Delta}}) & = &
  \text{\em exactly like \rulename{CVar}, with $\UNCOVERED$ instead of $\COVERED$} \\
 
\rulename{UGuard} & 
  \UNCOVERED & ({(p\leftarrow e)\:\vec{p}}) & ({\vtup{\Gamma}{\vec{u}}{\Delta}}) & = &
  \text{\em exactly like \rulename{CGuard}, with $\UNCOVERED$ instead of $\COVERED$} \\[4mm]

% ------------------------------ Divergent ----------------------------------
\multicolumn{7}{c}{\ruleform{ \ueliminated{\ps}{v} = \SB }} \\[2mm]
  \rulename{DNil} & 
  \ELIMINATED & {\emptyvec} & ({\vtup{\Gamma}{\emptyvec}{\Delta}}) & = & \varnothing \\

  \rulename{DConCon} ~~~~ &
  \ELIMINATED & ({(\cons{K_i}{\vec{p}})\:\vec{q}}) & ({\vtup{\Gamma}{(\cons{K_j}{\vec{u}})\:\vec{w}}{\Delta}}) & = &
  \left\{\begin{array}{l@@{\hspace{2mm}}l}
        \MAP~(\ZIPCON\: K_i)~(\eliminated{\vec{p}\:\vec{q}}{\vtup{\Gamma}{\vec{u}\:\vec{w}}{\Delta}}
           & \text{if } K_i = K_j \\
        \varnothing      
           & \text{if } K_i \neq K_j 
  \end{array}\right. \\

  \rulename{DConVar} &
  \ELIMINATED & ({(\cons{K_i}{\vec{p}})\:\vec{q}}) & ({\vtup{\Gamma}{x\:\vec{u}}{\Delta}}) & = &
    \multicolumn{2}{l}{\{~\vtup{\Gamma}{x\:\vec{u}}{\Delta\cup(x\termeq\bot)} \} \;\; \cup \;\;
    \eliminated{(\cons{K_i}{\vec{p}})\:\vec{q}}{\vtup{\Gamma'}{(\cons{K_i}{\YS{}})\:\vec{u}}{\Delta'}}} \\
  & &&  & & \hspace{-6pt} \begin{array}{ll}
          \text{where} & \YS{} \# \Gamma \quad \as \# \Gamma \quad (x{:}\tau_x) \in \Gamma \quad
                         K_i :: \forall\as. Q \Rightarrow \vec{\tau} \rightarrow \tau \\
                       & \Gamma' = \Gamma,\as,\vec{y}{:}\vec{\tau} \quad
                         \Delta' = \Delta \cup Q \cup \tau \typeeq \tau_x \cup x \termeq \cons{K_i}{\YS{}}
         \end{array} \\

  \rulename{DVar} &
  \ELIMINATED & ({x\:\vec{p}}) & ({\vtup{\Gamma}{u\:\vec{u}}{\Delta}}) & = &
  \text{\em exactly like \rulename{CVar}, with $\ELIMINATED$ instead of $\COVERED$} \\
 
  \rulename{DGuard} &
  \ELIMINATED & ({(p\leftarrow e)\:\vec{p}}) & ({\vtup{\Gamma}{\vec{u}}{\Delta}}) & = &
  \text{\em exactly like \rulename{CGuard}, with $\ELIMINATED$ instead of $\COVERED$} \\
\end{array}
\]

\caption{Clause Processing}
\label{fig:algorithm}
\end{figure*}

Our algorithm performs an abstract interpretation of the concrete dynamic semantics described in the last
section, and manipulates value vector abstractions instead of concrete value vectors. It follows
the scheme described in Section~\ref{sec:outline} and illustrated in Figure~\ref{fig:algorithm_outline}.
The key question is how $\mathit{patVectProc}$ works; that is the subject of this section, and constitutes
the heart of the paper.

\paragraph{Initialisation}
As shown in Figure~\ref{fig:algorithm_outline}, the algorithm is initialised with a set $\setuncovered{0}$
representing ``all values''. For every function
definition of the form:
\[\begin{array}{l}
  f @::@ \forall\as @.@ \tau_1 \to \ldots \to \tau_n \to \tau \\
  f~p_{11}~\ldots~p_{1n} = \ldots \\
  \qquad \ldots \\ 
  f~p_{m1}~\ldots~p_{mn} = \ldots
 \end{array}
\]
the initial call to $\mathit{patVectProc}$ will be with a singleton set:
\[ \setuncovered{0} =  \{ \vtup{\as,(x_1{:}\tau_1),\ldots,(x_n{:}\tau_n)}{x_1~\ldots~x_n}{\epsilon} \} \]

\noindent As a concrete example, the pattern match clauses of function @zip@ of 
type $\forall a b @.@ @[@a@]@ \to @[@b@]@ \to @[@(a,b)@]@$ from Section~\ref{sec:outline} 
will be initialised with 
\[ \setuncovered{0} =  \{ \vtup{a,b,(x_1{:}@[@a@]@),(x_2{:}@[@b@]@)}{x_1\;x_2}{\epsilon} \} \]
\noindent Notice that we use variables $x_i$, rather than the underscores used informally in 
Section~\ref{sec:outline}, so that we can record their types in $\Gamma$, and constraints
on their values in $\Delta$.

\paragraph{The main algorithm}
Figure~\ref{fig:algorithm} gives the details of $\mathit{patVectProc}$.
Given a pattern vector $\vec{p}$ and an incoming set $S$ of value vector abstractions,
$\mathit{patVectProc}$ computes the sets $\SC, \SU, \SB$ of covered, uncovered, and diverging
values respectively. As Figure~\ref{fig:algorithm} shows,
each is computed independently, in two steps. For each value vector abstraction $v$ in $S$:
\begin{itemize}
\item \emph{Use syntactic structure:} an auxiliary
function ($\COVERED, \UNCOVERED$ and $\ELIMINATED$)
identifies the subset of $v$ that is covered, uncovered, and divergent, respectively.
\item \emph{Use type and term constraints:} filter the returned set, retaining only those members
whose constraints $\Delta$ are satisfiable.
\end{itemize}
\noindent We describe each step in more detail, beginning with the syntactic function
for covered sets, $\SC$.

\paragraph{Computing the covered set} 

The function $\ucovered{\ps}{v}$ refines $v$ into those vectors that are
covered by the pattern vector $\ps$. It is defined inductively over the 
structure of $\ps$.

Rule \rulename{CNil} handles the case when both the pattern vector and the value vector are empty. In
this case the value vector is trivially covered.

Rule \rulename{CConCon} handles the case when both the pattern and value vector start
with constructors $K_i$ and $K_j$ respectively. 
If the constructors differ, then this particular
value vector {\em is not} covered and we return $\varnothing$.
If the constructors are the same, $K_i = K_j$, then we proceed 
recursively with the subterms $\vec{p}$ and $\vec{u}$ and the suffixes $\vec{q}$ and $\vec{w}$. 
We flatten these into a single
recursive call, and recover the structure afterwards with $\ZIPCON\:K_i$, defined thus:
        \[ \ZIPCON\: K\: (\vtup{\Gamma}{\vec{u}\:\vec{w}}{\Delta}) = \vtup{\Gamma}{(K\:\vec{u})\:\vec{w}}{\Delta} \]
where $\vec{u}$ matches the arity of $K$. 

Rule \rulename{CConVar} handles the case when the pattern vector starts with constructor $K_i$ and the value vector with variable $x$.
      In this case we refine $x$ to the most general abstraction that matches the constructor, $K_i\:\vec{y}$, where
      the variables $\YS{}$ are fresh for $\Gamma$, written $\YS{}\#\Gamma$. 
      Once the constructor shape for $x$ has been exposed, rule \rulename{CConCon} will fire to recurse
      into the pattern and value vectors. The constraint ($\Delta'$) used in the recursive call consists of the union of
      the original $\Delta$ with:
      \begin{itemize}
         \item $Q$; this is the constraint bound by the 
          constructor $K_i :: \forall\as @.@ Q \Rightarrow \vec{\tau} \rightarrow \tau$, which may for example 
          include type equalities (in the case of GADTs).
         \item $x \termeq K_i\;\YS{}$; this records a term-level equality in the constraint that could be used by guard expressions. 

         \item $\tau \sim \tau_x$, where $\tau_x$ is the type of $x$ in the environment $\Gamma$, and $\tau$ is the return type of the constructor.
         This constraint will be useful when dealing with GADTs as we  explain in Section~\ref{sec:gadt-constraints}.
\end{itemize}

Rule \rulename{CVar} applies when the pattern vector starts with a variable pattern $x$. This matches any value 
abstraction $u$, so we can proceed inductively in $\ps$ and $\vec{u}$. However $x$ may appear in some 
{\em guard} in the rest of the pattern, for example:
\begin{code}
   f x y | Nothing <- lookup x env = ...
\end{code}
To expose the fact that $x$ is bound to $u$ in subsequent
guards (and in the right-hand side of the clause, see Section~\ref{sec:nested}), 
rule \rulename{CVar} adds $x \termeq u$ to the constraints $\Delta$, and correspondingly extends $\Gamma$
to maintain the invariant that $\Gamma$  binds all variables free in $\Delta$.
Finally, $\MAP\:(\CONS\: u)$ prefixes each of the recursive results with $u$:
$$
\CONS \: u \: (\vtup{\Gamma}{\vec{u}}{\Delta}) = \vtup{\Gamma}{u\: \vec{u}}{\Delta}
$$

\noindent Rule \rulename{CGuard} deals with guards: see Section~\ref{sec:guards}.

Finally it is worth noting that the $\ucovered{\ps}{v}$ function
always returns an empty or singleton set, but we use the full set
notation for uniformity with the other functions.

\paragraph{Computing the uncovered and divergent sets}
The two other functions have a similar structure. Hence, we only highlight the
important differences. 

The function $\uuncovered{\ps}{v}$ returns those 
vectors that are {\em not covered} by the pattern vector $\ps$. When both the
pattern vector and value vector are empty then (we have seen in the previous case) 
that the value vector is covered and hence we return $\varnothing$. In rule 
\rulename{UConCon} there are two cases, just as in \rulename{CConCon}.
If the head constructors match ($K_i = K_j$), we simply recurse;
but if not, the entire value vector abstraction is uncovered, so we return it.
In case
\rulename{UConVar} we take the union of the uncovered sets for all refinements of
the variable $x$ to a constructor $K_j$; each can lead recursively through rule \rulename{UConCon} to uncovered cases.
To inform guards, we record the 
equality $x \termeq K_j\;\YS{}$ for each constructor. As in 
rule \rulename{CConVar} we also record a type constraint between the constructor return
type and the type of $x$ in $\Gamma$. (Section~\ref{sec:gadt-constraints})

The function $\ueliminated{\ps}{v}$ returns those vectors that diverge
when matching the pattern vector $\ps$. The empty value vector does not 
diverge \rulename{DNil}. The case for variables \rulename{DVar} is similar to 
previous cases. In the case of constructors in the head of the pattern vector as
well as the value vector \rulename{DConCon} there is no divergence either -- we either
recurse when the constructors match or else return the empty divergent set. When the clause 
starts with constructor $K_i$, and the vector with a variable $x$, rule \rulename{DConVar}
combines two different results: (a) the first result represents symbolically all vectors where $x$ diverges; 
(b) the second result recurses by refining $x$ to $K_i\;\YS{}$. In the first case we record the 
divergence of $x$ with a {\em strictness} constraint $(x \termeq \bot)$.
For the second case, we appeal recursively to the divergent set computation (We give more details on
the $\Delta'$ that we use to recurse in Section~\ref{sec:gadt-constraints}.)

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 

\paragraph{Filtering the results with constraints}

Function $\mathit{patVectProc}$ prunes the results of $\ucovered{\ps}{v}$, $\uuncovered{\ps}{v}$, and $\ueliminated{\ps}{v}$ 
that are semantically empty by appealing to an oracle judgement $\vdash_\textsc{Sat} (\vtup{\Gamma}{\vec{u}}{\Delta})$. 
In the next section we define ``semantically empty'' by giving a denotational semantics
to a value vector abstraction $\interp{v}$ as a set of concrete value vectors.

The purpose of $\vdash_\textsc{Sat}$ is to determine whether this set is empty. 
However, because satisfiability is undecidable in general (particularly when constraints involve term equivalence),
we have to be content with a decidable algorithm $\vdash_\textsc{Sat}$ that gives sound but incomplete
approximation to satisfiability:
\[ \not\vdash_\textsc{Sat} v ~~\Rightarrow~~ \interp{v} = \emptyset  \]
In terms of the outcomes (1-3) in Section~\ref{sec:outline}, 
``soundness'' means
\begin{enumerate}
\item If we do not warn that a set of clauses may be non-exhaustive,
then they are definitely exhaustive.
\item If we warn that a clause is redundant, then it definitely is redundant.
\item If we warn that a right-hand side of a non-redundant clause
is inaccessible, then it definitely is inaccessible.
\end{enumerate}
Since $\vdash_\textsc{Sat}$ is necessarily incomplete, the converse does not hold in general.
There is, of course, a large design space of less-than-complete implementations
for $\vdash_\textsc{Sat}$. Our implementation is explained in Section~\ref{s:implementation}.

Another helpful insight is this: during constraint generation
(Figure~\ref{fig:algorithm}) the sole purpose of adding constraints
to $\Delta$ is to increase the chance that $\vdash_\textsc{Sat}$ will
report ``unsatisfiable''.  It is always sound to
omit constraints from $\Delta$; so an implementation is free to trade off accuracy against
the size of the constraint set.

\subsection{Type Constraints from GADTs}\label{sec:gadt-constraints}

Rules \rulename{CConVar}, \rulename{UConVar}, and \rulename{DConVar} record {\em type equalities}
of the form $\tau \sim \tau_x$ between the value abstraction type ($\tau_x$) and the return type 
of the appropriate data constructor each time ($\tau$). 

Recording these constraints in \rulename{CConVar} and \rulename{UConVar} is important for reporting 
precise warnings when dealing with GADTs, as the following example demonstrates: 
\begin{code}
  data T a where
    TList :: T [a]
    TBool :: T Bool

  foo :: T c -> T c -> Int 
  foo TList _ = ...
  foo _ TList = ...
\end{code}
To determine $\setcovered{2}$, the covered set from the second equation,
we start from an initial singleton vector abstraction 
$\setuncovered{0} = \{ \vtup{\Gamma_0}{x_1\;x_2}{\epsilon}\}$ with $\Gamma = c,x_1{:}@T@\;c,x_2{:}@T@\;c$.
Next compute the uncovered set from the first clause, which (via \rulename{UConVar} 
and \rulename{UVar}) is $\setuncovered{1} = \{\vtup{\Gamma_1}{@TBool@\: x_2}{\Delta_1}\}$, where
\[\begin{array}{lcl}
    \Gamma_1 & = & \Gamma_0,a \\
    \Delta_1 & = & (x_1 \termeq @TBool@)\cup(@T@\;c \sim @T@\;@Bool@)
\end{array}\] 
Note the recorded type constraint for the uncovered constructor @TBool@ from rule \rulename{UConVar}. 
Next, from $\setuncovered{1}$, compute the covered set for the second equation
(via \rulename{CVar} and \rulename{CConVar}):
\[\begin{array}{rcl}
   \setcovered{2} & = & \covered{\_\;@TList@}{\vtup{\Gamma_1}{@TBool@\: x_2}{\Delta_1}}  \\ 
    & = & \{ \vtup{\Gamma_1,b}{@TBool@\;@TList@}{\Delta_2} \} \\
    & & \text{where}\;\Delta_2  = \Delta_1 \cup (x_2 \termeq @TList@)\cup(@T@\;c \sim @T@\:@[@b@]@)
\end{array}\]
Note the type constraint $@T@\;c \typeeq @T@\:[b]$ generated by rule \rulename{CConVar}. The final constraint
$\Delta_2$ is unsatisfiable and $\setcovered{2}$ is semantically empty, and the second equation 
is unreachable.
Unless \rulename{CConVar} or \rulename{UConVar} both record the type constraints we would 
miss reporting the second branch as redundant.

Rule \rulename{DConVar} also records term and type-level constraints in the recursive call. Indeed if 
the first case in that rule is deemed unsatisfiable by our oracle it is important to have a precise set
of constraints for the recursive call to detect possible semantic emptiness of the result.

%-------------------------------------------------------------------------------
\subsection{Guards} \label{sec:guards}

A major feature of our approach is that it scales nicely to handle \emph{guards},
and other syntactic extensions of pattern-matching supported by GHC. We briefly
reprise the development so far, adding guards at each step.

\paragraph{Syntax (Section~\ref{sec:syntax}).}
We begin with the syntax in Figure~\ref{fig:alg_syntax}:
a pattern $p$ can be a \emph{guard}, $g$, of the form $(p \leftarrow e)$.
This syntax is very general.  For example, the clauses of @abs1@
(Section~\ref{sec:challenge-guards}) would desugar to:

>    x (True <- x<0)       -> -x
>    x (True <- otherwise) -> x

Notice that these \emph{two}-element pattern vectors match against \emph{one} argument;
a guard $(p \leftarrow e)$ matches against $e$, not against an argument.

GHC's pattern guards are equally easy to represent; there is no desugaring to do!
However, the syntax of Figure~\ref{fig:alg_syntax} is more expressive
than GHC's pattern guards, because it allows a guard to
occur \emph{arbitrarily nested inside a pattern}.
This allow us to desugar literal patterns and view patterns.  For example, 
consider the Haskell function

> f ('x', []) = True
> f _         = False

The equality check against the literal character @'x'@ must occur \emph{before}
matching the second component of the tuple, so that the call $(@f@\,@('y',@,\bot@)@)$ returns
@False@ rather than diverging.  With our syntax we can desugar @f@ to these
two clauses:

>  (a (True <- a=='x'), [])  -> True
>  c                         -> False

Note the nested guard @True <- a=='x'@.
It is not hard to see how to desugar view patterns in a similar way; see the extended version of this paper~\cite{gadtpm}. %Appendix~\ref{pm:translation}.

\paragraph{Clause processing (Section~\ref{s:formalisation:core}).}
It is easy to extend the clause-processing algorithm to accommodate guards.
For example, equation \rulename{CGuard} in Figure~\ref{fig:algorithm}
deals with the case when the first pattern in the pattern vector is a guard $(p \leftarrow e)$.
We can simply make a recursive call to $\COVERED$ adding $p$ to the front of 
the pattern vector, and a fresh variable $y$ to the front of the value abstraction.
This variable $y$ has the same type $\tau$ as $e$, and we add a term-equality
constraint $y \termeq e$ to the constraint set.  Finally, the $\MAP\:\TAIL$
removes the guard value from the returned value vector:
\[
\TAIL\:(\vtup{\Gamma}{u\,\vec{us}}{\Delta}) = \vtup{\Gamma}{\vec{us}}{\Delta})
\]

That's all there is to it!  The other cases are equally easy. However, it is illuminating
to see how the rules work in practice.  Consider again function @abs1@ in 
Section~\ref{sec:challenge-guards}.  We may compute (laboriously) as follows:
$$
\begin{array}{r@@{\hspace{1mm}}c@@{\hspace{1mm}}l}
\setuncovered{0} & = & \{ \vtup{v{:}@Int@}{v}{} \} \\
\setuncovered{1} & = & \uncovered{x\,(@True@ \leftarrow x@<@0)}{\vtup{v{:}@Int@}{v}{}} \\
 & = & \text{(apply \rulename{UVar})} \\
 &   & \MAP\:(\CONS\:v)\: (\uncovered{@True@ \leftarrow v@<@0}{\vtup{v{:}@Int@}{\emptyvec}{x \termeq v}}) \\
 & = & \text{(apply \rulename{UGuard})} \\
 &   & \MAP\:(\CONS\: v)\: (\MAP\:\TAIL \\
 & & \quad (\uncovered{@True@}{\vtup{v{:}@Int@, y{:}@Bool@}{y}{x \termeq v, y \termeq v @<@ 0}}) \\
 & = & \text{(apply \rulename{UConVar}; the @True@/@True@ case yields $\varnothing$)} \\
 &   & \MAP\:(\CONS\: v)\: (\MAP\:\TAIL\: (\MAP\:(\CONS\:y) \\
 & & \quad (\uncovered{@True@}{v{:}@Int@, y{:}@Bool@ \vdash @False@ \\ % Inlined vtup to make it fit
 & & \hspace{18mm} \triangleright\: x \termeq v, y \termeq v @<@ 0,y\termeq @False@}) \\
 & = & \text{(apply \rulename{UConCon} with $K_i \not= K_j$, and do the $\MAP$s)} \\
 &   & \{ \vtup{v{:}@Int@, y{:}@Bool@}{v}{x \termeq v, y \termeq v @<@ 0, y\termeq @False@} \} 
\end{array}
$$
This correctly characterises the uncovered values as those $v{:}@Int@$ for which $v@<@0$ is @False@.

%-------------------------------------------------------------------------------
\subsection{Extension 1: Smarter Initialisation}

In the previous section, we always initialised $\setuncovered{0}$ with the
empty constraint, $\Delta = \epsilon$.  But consider these definitions:
\begin{code}
type family F a               data T a where
type instance F Int = Bool      TInt  :: T Int
                                TBool :: T Bool
\end{code}
Datatype @T@ is a familiar GADT definition. @F@ is a {\em type family}, or type-level
function, equipped with an instance that declares @F Int = Bool@. 
Given these definitions, is the second clause of @f@ below redundant?
\begin{code}
f :: F a ~ b => T a -> T b -> Int
f TInt  TBool = ...
f TInt  x     = ...
f TBool y     = ...
\end{code}
Function @f@ matches the first argument with @TInt@, 
yielding the local type equality $@a@ \sim @Int@$.
Using this fact, together with the signature 
constraint $@F a@ \sim @b@$ and the top-level equation
@F Int = Bool@, we can deduce that $@Bool@ \sim @b@$,
and hence the second clause is in fact redundant. 
In this reasoning we had to use the quantified 
constraint $@F a@ \sim @b@$ from the signature of @f@. Hence the initial value abstraction $\setuncovered{0}$
for this pattern match should include constraints from the function signature:
\[ U_0 = \{ \vtup{a,b,(x_1{:}@T@\;a),(x_2{:}@T@\;b)}{x_1\;x_2}{\mathbf{@F@\;a\sim b}} \} \]

\subsection{Extension 2: Nested Pattern Matches} \label{sec:nested}

Consider this definition:
\begin{code}
  f [] = ...
  f x  = ...(case x of { w:ws -> e })...
\end{code}
The clauses of @f@ and those of the inner @case@ expression are entirely 
disconnected.  And yet we can see that both of the inner
@case@ expressions are exhaustive, because the $@x@=@[]@$ case is handled
by the first equation.

Happily there is a principled way to allow the inner @case@ to take
advantage of knowledge from the outer one: \emph{gather the constraints
from the covered set of the outer pattern match, propagate them inwards, and use
them to initialise $\setuncovered{0}$ for the inner one}.
In this example, we may follow the algorithm as follows:
\[
\begin{array}{r@@{\hspace{1mm}}c@@{\hspace{1mm}}l}
\setuncovered{0}^{\,f} & = & \{ \vtup{a,v{:}@[@a@]@}{v}{} \} \\
\setuncovered{1}^{\,f} & = & \{ \vtup{a,v{:}@[@a@]@,v_1{:}a,v_2{:}@[@a@]@}{(v_1@:@v_2)}{} \} \\
\setcovered{2}^{\,f}   & = & \{ \vtup{a,v{:}@[@a@]@,v_1{:}a,v_2{:}@[@a@]@,x{:}@[@a@]@}{(v_1@:@v_2)}{x \termeq v_1@:@v_2} \}
\end{array}
\]
Propagate $\setcovered{2}^{\,f}$ inwards to the @case@ expression.
Now initialise the $\setuncovered{0}^{\,case}$ for the @case@ expression thus:
\[
\setuncovered{0}^{\,case} = \{ (\vtup{\Gamma}{x}{\Delta})
    \mid (\vtup{\Gamma}{\vec{u}}{\Delta}) \in \setcovered{2}^{\,f} \}
\]
You can see that the $\Delta$ used for the inner @case@ will
include the constraint $x=v_1@:@v_2$ inherited from $\setcovered{2}^{\,f}$,
and that in turn can be used by $\vdash_\textsc{Sat}$ to show that the @[]@
missing branch of the @case@ is inaccessible.
Notice that $\setuncovered{0}$ many now have more than one element; until now
it has always been a singleton.

The same idea works for type equalities, so that type-equality
knowledge gained in an outer pattern-match can be carried inwards in
$\Delta$ and used to inform inner pattern matches.  Our implementation
does exactly this and solves the existing GHC ticket \#4139 that
needs this functionality.  (Caveat: our implementation so far 
only propagates type constraints, not term constraints.)

%===============================================================================
\section{Meta-theory} \label{sec:semantics}

In order to formally relate the algorithm to the dynamic semantics of pattern
matching, we first formalise the latter as well as the semantics of the value
abstractions used by the former.

%-------------------------------------------------------------------------------
\subsection{Value Abstractions}
As outlined in Section~\ref{sec:outline} a value abstraction denotes
a set of values.
Figure~\ref{msrc_interpretation_of_value_abstractions} formalises this notion. 

As the Figure shows, the meaning of a closed value abstraction
$\vtup{\Gamma}{\vec{u}}{\Delta}$ is the set of all type-respecting
instantiations of $\vec{u}$ to a vector of (closed) values $\vec{V} =
\theta(\vec{u})$, such that the constraints $\theta(\Delta)$ are
satisfied.  The judgement $\models \Delta$ denotes the logical
entailment of the (closed) constraints $\Delta$; we omit the details
of its definition for the sake of brevity.

A ``type-respecting instantiation'', or denotation,
of a type environment $\Gamma$
is a substitution $\theta$ whose domain is that of $\Gamma$; it maps
each type variable $a \in \Gamma$ to a closed type; and each
term variable $x{:}\tau \in \Gamma$ to a closed value $V$
of the appropriate type $\vdash_v V : \tau$.
The syntax of closed types and values is given in 
Figure~\ref{msrc_interpretation_of_value_abstractions}, as is the
typing judgement for values.
For example, 
\[ 
\begin{array}{l}
\interp{ \{\vtup{@a@, @b@, @x@:@a@, @y@:@b@}{@x y@}{@a@ \typeeq @Bool@, @b@ \typeeq @()@}\} } \\
= \begin{array}[t]{rlllllllll}
  \{ & @True@  & @()@ & , & @False@ & @()@ & , & \bot    & @()@ & ,  \\
     & @True@  & \bot & , & @False@ & \bot & , & \bot    & \bot & \}  
  \end{array}
\end{array}
\]

%-------------------------------------------------------------------------------
\subsection{Pattern Vectors}
Figure~\ref{msrc_interpretation_of_clauses} formalises the dynamic
semantics of pattern vectors.

The basic meaning $\interp{\ps}^\theta$ of a pattern vector $\ps$ is a
function that takes a vector of values $\vec{V}$ to a matching result $M$. There
may be free variables in (the guards of) $\ps$; the given substitution $\theta$
binds them to values. The matching result $M$ has the form $\TRUE$, $\FALSE$ or $\bot$
depending on whether the match succeeds, fails or diverges. 

Consider matching the pattern vector @x (True <- x > y)@, where @y@ is bound to @5@, against the value @7@; this match
succeeds. Formally, this is expressed thus:
\[ \interp{@x (True <- x > y)@}^{[@y@ \mapsto @5@]}(@7@) = \TRUE \]

For comparing with our algorithm, this formulation of the dynamic semantics is not ideal:
the former acts on whole sets of value vectors (in the form of value abstractions) at a time, while
the latter considers only one value vector at a time. To bridge this gap, 
$\interp{\ps}$ lifts $\interp{\ps}^\epsilon$ from an individual
value vector $\vec{V}$ to a whole set $S$ of value vectors. It does so by
partitioning the set based on the matching outcome, which is similar to the behaviour of our algorithm.

\begin{figure}[t]
\centering
\[
  \begin{array}{l@@{\hspace{1mm}}ll}
     \tau_c & ::= T\:\overline{\tau}_c \mid \tau_c \rightarrow \tau_c & \text{Closed Monotypes} \\
     V, W   & ::= K\:\vec{V} \mid \lambda x.e \mid \bot & \text{Values}  \\
     M      & ::= \TRUE \mid \FALSE \mid \bot & \text{Matching Result} \\
     \mathscr{S}, \mathscr{C}, \mathscr{U}, \mathscr{U} & ::= \bar{\vec{V}} & \text{Set of value vectors}
  \end{array}
\]
\[ \textbf{Denotation of expressions} \]
\[\ruleform{ \einterp{e} = V } \]
\[ \text{(definition omitted)} \]
\[ \textbf{Denotation of value abstractions} \]
\[\ruleform{ \interp{S} = \overline{\vec{V}}  } \]
\[
  \begin{array}{c}
    \interp{S} = \{ \theta(\vec{u}) \mid (\vtup{\Gamma}{\vec{u}}{\Delta}) \in S,\; \theta \in \interp{\Gamma}, \; \models \theta(\Delta) \} 
  \end{array}
\]
\[ \textbf{Denotation of typing environments} \]
\[ \ruleform{\interp{\Gamma} = \bar{\theta}} \]
\[
\begin{array}{lcl}
\interp{\epsilon}           & = & \{ \epsilon \} \\
\interp{x : \tau_c, \Gamma} & = & \{\theta \cdot [ x \mapsto V ]      ~\mid~ \vdash_v V : \tau_c, \theta \in \interp{\Gamma}\} \\
\interp{a, \Gamma}          & = & \{\theta \cdot [ a \mapsto \tau_c ] ~\mid~ \theta \in \interp{[ a \mapsto \tau_c ](\Gamma)}\} \\
\end{array}
\]
\[ \textbf{Well-typed values} \]
\[\ruleform{ \vdash_v V : \tau_c }  \]
\[
\begin{array}{c}
  \prooftree
    % Empty here
  \justifies
    \vdash_v \bot : \tau_c
  \using
    \textsc{Bot}
  \endprooftree 

\quad\quad

  \prooftree
    x : \tau_{c,1} \vdash e : \tau_{c,2}
  \justifies
    \vdash_v \lambda x.e : \tau_{c,1} \rightarrow \tau_{c,2}
  \using
    \textsc{Fun}
  \endprooftree 

\\ \\

  \prooftree
    \begin{array}{ll}
      K :: \forall \overline{a}\: \overline{b}. Q \Rightarrow \overline{\tau} \to T\:\overline{a} & \models \theta(Q) \\
      \theta = [\overline{a \mapsto \tau_{c_i}}, \overline{b \mapsto \tau_{c_j}}] & \vdash_v V_i : \theta(\tau_i) \quad (\forall i) \\
    \end{array}
  \justifies
    \vdash_v K\:\vec{V} : T\:\vec{\tau}_{c_i}
  \using
    \textsc{Con}
  \endprooftree
\end{array}
\]

%\paragraph{Interpretation 1: Coverage for one value vector}
\[ \textbf{Denotation of patterns} \]
\[ \ruleform{\interp{\ps}^\theta :: \vec{V} \to M} \]
\[
\begin{array}{@@{}l@@{\hspace{1mm}}l}
  % empty
  \pinterpm{\emptyvec}{\theta}{\emptyvec} & = \TRUE \\

  % var-any
  \pinterpm{x\:\vec{p}}{\theta}{V\:\vec{V}} & = \pinterpm{\vec{p}}{[x \mapsto V] \cdot \theta}{\vec{V}} \\

  % guard-any
  \pinterpm{(p \leftarrow e)\:\vec{p}}{\theta}{\vec{V}} & = \pinterpm{p\:\vec{p}}{\theta}{\einterp{\theta(e)}\:\vec{V}} \\

  % con-con
  \pinterpm{(K_i\:\vec{p})\:\vec{q}}{\theta}{(K_j\:\vec{V})\vec{W}} & =
    \left\{
      \begin{array}{@@{}ll}
        \pinterpm{\vec{p}\:\vec{q}}{\theta}{\vec{V}\:\vec{W}} & \text{, if } K_i =    K_j \\
        \FALSE                                                & \text{, if } K_i \neq K_j \\
      \end{array}
    \right. \\

  % con-bot
  \pinterpm{(K_i\:\vec{p})\:\vec{q}}{\theta}{\bot\:\vec{V}} & = \bot \\

\end{array}
\]
% %\paragraph{Interpretation 2: Coverage for many value vectors (partition)}
\[ \ruleform{ \interp{\ps} :: \bar{\vec{V}} \to \langle \bar{\vec{V}}_c, \bar{\vec{V}}_u, \bar{\vec{V}}_\bot \rangle} \]
\[
\begin{array}{lcl}
  \interp{\ps}(\mathscr{S})
   & = & \langle \{ \vec{V} \mid \vec{V} \in \mathscr{S} \text{ where } \pinterpm{\ps}{\epsilon}{\vec{V}}  = \TRUE  \} \\
   &   &       , \{ \vec{V} \mid \vec{V} \in \mathscr{S} \text{ where } \pinterpm{\ps}{\epsilon}{\vec{V}}  = \FALSE \} \\
   &   &       , \{ \vec{V} \mid \vec{V} \in \mathscr{S} \text{ where } \pinterpm{\ps}{\epsilon}{\vec{V}} = \bot   \}
                            \rangle \\
\end{array}
\]
\caption{Semantics of Value Abstractions and Patterns}
\label{msrc_interpretation_of_value_abstractions}
\label{msrc_interpretation_of_clauses}
\end{figure}

%-------------------------------------------------------------------------------
\subsection{Correctness Theorem}
Now we are ready to express the correctness of the algorithm with respect to the dynamic
semantics. The algorithm is essentially an abstraction of the dynamic
semantics. Rather than acting on an infinite set of values, it acts on a
finite representation of that set, the value abstractions. Correctness amounts
to showing that the algorithm treats the abstract set in a manner that faithfully reflects
the way the dynamic semantics treats the corresponding concrete set.
In other words, it should not matter whether we run the algorithm on an abstract set $S$ and
interpret the abstract result $\langle C, U, D \rangle$ as sets of concrete
values $\langle \mathscr{C}, \mathscr{U}, \mathscr{D}\rangle$, or whether we first
interpret the abstract set $S$ as a set $\mathscr{S}$ of concrete values and then run the
concrete dynamic semantics on those.

This can be expressed concisely as a commuting diagram:
\[
\xymatrix@@C=6em{
S \ar[d]_-{\interp{\cdot}} \ar[r]^-{\mathit{patVectProc}(\ps)} & \langle C, U, D \rangle \ar[d]^-{\interp{\cdot}}\\
\mathscr{S} \ar[r]_-{\interp{\ps}} & \langle \mathscr{C}, \mathscr{U}, \mathscr{D}\rangle}
\]

This diagram allows us to interpret the results of the algorithm. For instance, if we choose $s$ to cover
all possible value vectors and we observe that $C$ is empty, we can conclude that no value vector successfully matches $\ps$.

To state correctness precisely we have to add the obvious formal fine print about types:
The behaviour of pattern matching is only defined if:
\begin{enumerate}
\item the pattern vector $\ps$ is well-typed,
\item the value vector $\vec{V}$ and, by extension,
      the value set $\mathscr{S}$ and the abstract value set $S$ are well-typed, and
\item the types of pattern vector $\ps$ and value vector $\vec{V}$ correspond.
\end{enumerate}
The first condition we express concisely with the judgement $Q ;
\Gamma \vdash \ps : \vec{\tau}$, which expresses that the pattern 
vector $\ps$ has types $\vec{\tau}$ for a type environment
$\Gamma$ and given type constraints $Q$. 

For the second condition, we first consider the set of all values value vectors
compatible with types $\vec{\tau}$, type environment $\Gamma$ and given type
constraints $Q$.  This set can be compactly written as the interpretation
$\interp{S^*}$ of the value abstraction $S^* = \{ \vtup{\Gamma,
\vec{x}:\vec{\tau}}{\vec{x}}{Q} \}$. Any other well-typed value vectors $\vec{V}$ 
must be contained in this set: $\vec{V} \in \interp{S^*}$. Similarly, $\mathscr{S} \subseteq \interp{S^*}$
and $\interp{S} \subseteq \interp{S^*}$

Finally, the third condition is implicitly satisfied by using the same types
$\vec{\tau}$, type environment $\Gamma$ and given type constraints $Q$.

Wrapping up we formally state the correctness theorem as follows:
\begin{theorem}[Correctness]
\begin{multline*}
 \forall \Gamma, Q, \ps, \vec{\tau}, S:~~ 
    Q ; \Gamma \vdash \ps : \vec{\tau} ~\wedge~ \interp{S} \subseteq \interp{\{ \vtup{\Gamma,
\vec{x}:\vec{\tau}}{\vec{x}}{Q} \}} \\
   \Longrightarrow~~ \interp{\mathit{patVectProc}(\ps,S)}  =  \interp{\ps}{\interp{S}}   
\end{multline*}
\end{theorem}

%===============================================================================
% Section 6 (Implementation details)
\section{Implementation}\label{s:implementation}

This section describes the current implementation of our algorithm in GHC and
possible improvements.

The pattern-match warning pass runs once type inference is complete.
At this stage the syntax tree is richly decorated with type
information, but has not yet been desugared.  Warnings will therefore
refer to the program text written by the user, and not so some
radically-desugared version. Actually the pattern-match warning
generator is simply called by the desugarer, just before it desugars
each pattern match.

The new pattern match checker takes 504 lines of Haskell, compared to 588
lines for the old one.  So although the new checker is far more capable,
it is of comparable code size.

%-------------------------------------------------------------------------------
\subsection{The Oracle}\label{s:sat_solvers}

The oracle judgement $\vdash_\textsc{Sat}$ is treated as a black box by the
algorithm. As long as it is conservative, any definition will do, even
accepting all constraints. Our implementation does quite a bit better than
that.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Type-level constraints}
For type constraints we simply re-use the powerful
type-constraint solver, which GHC uses for type
inference~\cite{outsidein}.
Hence, inconsistency of type constraints is defined uniformly and
our oracle adapts automatically to any changes in the type system,
such as type-level functions, type-level arithmetic, and so on.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Term-level constraints} 
Currently, our oracle implementation for term-level constraints is
vestigial. It is specialised for trivial guards of the form |True| and knows
that these cannot fail. Thus only conjunctions of constraints of the form $y
\termeq @True@, y \termeq @False@$ are flagged as inconsistent. This enables us
to see that @abs1@ (Section~\ref{sec:challenge-guards}) is exhaustive, but not
@abs2@.
There is therefore plenty of scope for
improvement, and various powerful term-level solvers, such as Zeno~\cite{zeno} and
HipSpec~\cite{hipspec}, could be used to serve the oracle.

%-------------------------------------------------------------------------------
\subsection{Performance Improvements}
 
We have optimised the presentation of our algorithm in Section~\ref{sec:formal}
for clarity, rather than runtime performance. Even though we cannot improve
upon the asymptotic worst-case time complexity, various measures can improve the
average performance a big deal.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Implicit solving}
The formulation of the algorithm in Section~\ref{sec:algorithm} generates type
constraints for the oracle with a high frequency. For instance, rule~\rulename{CConVar} of the
$\COVERED$ function generates a new type equality constraint $\tau \sim \tau_x$
every time it fires, even for Haskell'98 data types.

While there are good reasons for generating these constraints in general, we
can in many cases avoid generating them explicitly and passing them on to the oracle. Instead, we can handle them immediately and much more
cheaply. One important such case is covered by the specialised variant of rule
\rulename{CConVar} in Figure~\ref{fig:algorithm:special}: the type  $\tau_x$
has the form $T\:\vec{\tau}_x$, where $T$ is also the type constructor of the
constructor $K_i$. This means that the generated type constraint $\tau \sim
\tau_x$ actually has the form $T\:\as \sim T\:\vec{\tau}_x$. We can simplify
this constraint in two steps. Firstly, we can decompose it into simpler type
equality constraints $a_i \sim \tau_{x,i}$, one for each of the type
parameters. Secondly, since all type variables $\as$ are actually fresh, we can
immediately \emph{solve} these constraints by substituting all occurrences of
$\as$ by $\vec{\tau}_x$. Rule \rulename{CConVar} incorporates this simplification
and does not generate any type constraints at all for Haskell'98 data types.


\newcommand{\bs}{\vec{b}}

\begin{figure*}[t]
\[ \begin{array}{lllllll}
\rulename{CConVar'}\quad & 
  % con-var
  \COVERED & ({(\cons{K_i}{\vec{p}})\:\vec{q}}) & ({\vtup{\Gamma}{x\:\vec{u}}{\Delta}}) & = &
    \covered{(\cons{K_i}{\vec{p}})\:\vec{q}}{\vtup{\Gamma'}{(\cons{K_i}{\YS{}})\:\vec{u}}{\Delta'}} \\
   & &&  & & \hspace{-6pt} \begin{array}{ll}
            \text{where} & \YS{} \# \Gamma \quad \bs \# \Gamma \quad (x{:}T\:\vec{\tau}_x) \in \Gamma 
                         \quad K_i :: \forall \as,\bs. Q \Rightarrow \vec{\tau} \rightarrow T\:\as \\
                         & \theta = [\as \mapsto \vec{\tau}_x] \quad \Gamma' = \Gamma,\bs, \vec{y}{:}\theta(\vec{\tau}) \\
                         & \Delta' = \Delta \cup \theta(Q) \cup x \termeq \cons{K_i}{\YS{}} 
\end{array}\end{array}\]
\caption{Specialised Clause Processing}
\label{fig:algorithm:special}
\end{figure*}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Incremental solving}
Many constraint solvers, including the \OutsideIn{X} solver, support an incremental interface: 

< solve :: Constraint -> State -> Maybe State

In the process of checking given constraints $C_0$ for satisfiability, they
also normalise them into a compact representation. When the solver believes the
constraints are satisfiable, it returns their normal form: a \emph{state}
$\sigma_0$. When later the conjunction $C_0 \wedge C_1$ needs to be checked, we
can instead pass the state $\sigma_0$ together with $C_1$ to the solver.
Because $\sigma_0$ has already been normalised, the solver can process the
latter combination much more cheaply than the former.

It is very attractive for our algorithm to incorporate this incremental
approach, replace the constraints $\Delta$ by normalised solver states $\sigma$
and immediately solve new constraints when they are generated. Because the
algorithm refines step by step one initial value abstraction into many different
ones, most value abstractions share a common prefix of constraints. By using
solver states for these common prefixes, we share the solving effort among all refinements
and greatly save on solving time. Moreover, by finding inconsistencies early, we can 
prune eagerly and avoid refining in the first place.

%===============================================================================
\section{Evaluation}\label{sec:evaluation}

Our new pattern checker addresses the three challenges laid out in
Section~\ref{sec:challenge}: GADTs, laziness, and guards.  However in
our evaluation, only the first turned out to be significant.
Concerning laziness, none of our test programs triggered the warning
for a clause that is irredundant, but has an inaccessible right hand
side; clearly such cases are rare! Concerning guards, our prototype
implementation only has a vestigial term-equality solver, so until we
improve it we cannot expect to see gains.

For GADT-rich programs, however, we do hope to see
improvements. However, many programs do not use GADTs at all; and
those that do often need to match over all constructors of the type
anyway.  So we sought test cases by asking the Haskell @libraries@
list for cases where the authors missed accurate warnings for
GADT-using programs. This has resulted in identifying 9 hackage packages
and 3 additional libraries, available on GitHub.\footnote{
\href{https://github.com/amosr/merges/blob/master/stash/Lists.hs}{https://github.com/amosr/merges/blob/master/stash/Lists.hs}\\
\href{https://github.com/gkaracha/gadtpm-example}{https://github.com/gkaracha/gadtpm-example}\\
\href{https://github.com/jstolarek/dep-typed-wbl-heaps-hs}{https://github.com/jstolarek/dep-typed-wbl-heaps-hs}\\
}

We compared three checkers.  The baseline is, of course, vanilla GHC.
However, GHC already embodies an \emph{ad hoc} hack to improve
warning reports for GADTs, so we ran GHC two ways: both with (GHC-2)
and without (GHC-1) the hack.
Doing so gives a sense of how effective the \emph{ad hoc} approach
was compared with our new checker.

For each compiler we measured:
\begin{itemize}
\item \emph{The number of missing clauses (M).}
The baseline compiler GHC-1 is conservative, and reports too many missing 
clauses; so a lower M represents more accurate reporting.
\item \emph{The number of redundant (R) clauses.}
The baseline compiler is conservative, and reports too few redundant
clauses; so a higher R represents more accurate reporting.
\end{itemize}

The results are presented in Table~\ref{fig:results}. They clearly show that
the ad-hoc hack of GHC-2 was quite succesful at eliminating unnecessary missing
pattern warnings, but is entirely unable to identify redundant clauses. The
latter is where our algorithm shines: it identifies 38 pattern matches with
redundant clauses, all of them catch-all cases added to suppress erroneous warnings. We also see a good
reduction (-27) of the unnecessary missing pattern warnings. The remaining spurious missing pattern warnings
in \textit{accelerate} and \textit{d-bus} involve pattern guards and view patterns;  these can be eliminated
by upgrading the term-level reasoning of the oracle.

\begin{table}[t]
\[
\begin{array}{lrrrrrrr}
   & & \multicolumn{2}{c}{\textbf{GHC-1}} & \multicolumn{2}{c}{\textbf{GHC-2}} & \multicolumn{2}{c}{\textbf{New}} \\
  \cline{3-8} \\
  \textbf{Hackage Packages} & \textbf{LoC} & \textbf{M} & \textbf{R} & \textbf{M} & \textbf{R} & \textbf{M} & \textbf{R} \\
  \hline
  \textit{accelerate}     & 11,393 & 11 & 0 & 9  & 0 & 8   & 14 \\
  \textit{ad}             &  1,903 & 2  & 0 & 0  & 0 & 0  & 6  \\
  \textit{boolsimplifier} &    256 & 10 & 0 & 0  & 0 & 0  & 0  \\
  \textit{d-bus}          &  2,753 & 45 & 0 & 42 & 0 & 16 & 1  \\
  \textit{generics-sop}   &  1,008 & 0  & 0 & 0  & 0 & 0  & 3  \\
  \textit{hoopl}          &  2,147 & 33 & 0 & 0  & 0 & 0  & 3  \\
  \textit{json-sop}       &    393 & 0  & 0 & 0  & 0 & 0  & 2  \\
  \textit{lens-sop}       &    280 & 2  & 0 & 0  & 0 & 0  & 2  \\
  \textit{pretty-sop}     &     27 & 0  & 0 & 0  & 0 & 0  & 1  \\
  \\
   \textbf{Additional tests} & \textbf{LoC} & \textbf{M} & \textbf{R} & \textbf{M} & \textbf{R} & \textbf{M} & \textbf{R} \\

  \hline
  \textit{lists}        & 66  & 1 & 0 & 0 & 0 & 0  & 3 \\
  \textit{heterogeneous lists}       & 38  & 0 & 0 & 0 & 0 & 0  & 2 \\
  \textit{heaps}         & 540 & 3 & 0 & 0 & 0 & 0  & 1 \\
\end{array}
\]
\caption{Results}
\label{fig:results}
\end{table}

\paragraph{Erroneous suppression of warnings}
We have found three cases where the programmer has erroneously added clauses to
suppress warnings. We have paraphrased one such example in terms of the |Vect n a|
type of Section~\ref{introduction}.

> data EQ n m where
>   EQ :: n ~ m => EQ n m
> 
> eq :: Vect n a -> Vect m a -> EQ n m -> Bool
> eq  VN       VN        EQ = True
> eq (VC x xs) (VC y ys) EQ = x == y && eq xs ys
> eq VN        (VC _ _)  _  = error "redundant"
> eq (VC _ _)  VN        _  = error "redundant"

This example uses the |EQ n m| type as a witness for
the type-level equality of |n| and |m|. This equality
is exposed by pattern matching on |EQ|. Hence, the third and fourth
clauses must be redundant. After all, we cannot possibly have an equality
witness for @Zero ~ Succ n@. Yes, we can: that witness is $\bot :: @EQ Zero (Succ n)@$
and it is not ruled out by the previous clauses. Indeed, calls of the form
$@eq@\,@VN@\, (@VC@\, x\, xs)\, \bot$  and $@eq@\, (@VC@\, x\,
xs)\,@VN@\, \bot$ are not covered by the first two clauses and hence rightly reported missing.
The bottoms can be flushed out by moving the equality witness to the front of the
argument list and matching on it first. Then the first two clauses suffice.

\paragraph{GHC tickets}
With our new algorithm we have also been able to close nine GHC tickets
related to GADT pattern matching (\ticket{3927}, \ticket{4139}, \ticket{6124}, \ticket{8970})
and literal patterns (\ticket{322}, \ticket{2204}, \ticket{5724}, \ticket{8016}, \ticket{8853}).

%===============================================================================
% Section 7 (Related work)
\section{Related Work} \label{sec:related}

\subsection{Compiling Pattern Matching}

There is a large body of work concerned with the {\em efficient compilation} of pattern 
matching, for strict and lazy languages~\cite{Laville:lpm,maranget:lazy-pm,lazypm,maranget:decision-trees}. 
Although superficially related, these works focus on an entirely different problem,
one that simply does not arise for us.  Consider
\begin{code}
f True  True  = 1
f _     False = 2
f False True  = 3
\end{code}
In a strict language one can choose whether to begin by matching the first argument or the second;
the choice affects only efficiency, not semantics.  In a lazy language the choice affects
semantics; for example, does $@f@\;(\bot,@False@)$ diverge, or return @2@?
Laville and Maranget suggest choosing a match order that makes @f@ 
maximally defined \cite{maranget:lazy-pm}, and they explore the ramifications of this choice.

However, Haskell does not offer this degree of freedom; it fixes a top-to-bottom and
left-to-right order of evaluation in pattern match clauses.

\subsection{Warnings for Simple Patterns}\label{sec:related-simple}

We now turn our attention to \emph{generating warnings} for inexhaustive or redundant patterns.
For simple patterns (no guards, no GADTs) there are several related works.
The most closely-related is Maranget's elegant algorithm for
detecting missing and redundant (or ``useless'') clauses~\cite{maranget:warnings}.
Maranget recursively defines a
predicate that determines whether there could be any vector of values
$v$ that matches pattern vector $\ps$, without matching any pattern
vector row in a matrix $P$, $U_{req}(P,\ps)$, and answers both
questions of exhaustiveness (query ${\cal U}_{req}(P,\_)$) and
redundancy (query ${\cal U}_{req}(P^{1..(j-1)},\ps_j)$ where
$P^{1..(j-1)}$ corresponds to all previous clauses). Our algorithm has
many similarities (e.g. in the way it expands constructor patterns)
but is more incremental by propagating state from one clause to the next
instead of examining all previous clauses for each clause. 

Maranget's algorithm does not deal with type constraints
(as those arising from GADTs), nor guards and nested patterns that
require keeping track of $\Delta$ and environment $\Gamma$. Finally
the subtle case of an empty covered set but a non-empty divergent set
would not be treated specially (and the clause would be considered as
non-redundant, though it could only allow values causing divergence).

Krishnaswami~\cite{krisnaswami} accounts for exhaustiveness and redundancy
checking as part of formalisation of pattern matching in terms of the focused
sequent calculus. His approach assumes a left-to-right ordering in the translation of ML
patterns, which is compatible with Haskell's semantics.

Sestoft~\cite{sestoft} focuses on compiling pattern matches for a simply-typed
variant of ML, but his algorithm also identifies inexhaustive matches and
redundant match rules as a by-product.

%-------------------------------------------------------------------------------
\subsection{Warnings for GADT Patterns}

OCaml and Idris both support GADTs, and both provide some GADT-aware
support for pattern-match checking.  No published work describes the
algorithm used in these implementations.

\paragraph{OCaml}
When Garrigue and Le Normand introduced
GADTs to the OCaml language~\cite{ocamlgadts}, they also extended the checking
algorithm. It eliminates the ill-typed uncovered cases proposed by OCaml's original
algorithm. However, their approach does not identify clauses that are redundant
due to unsatisfiable type constraints.  For instance, the third clause in
@f@ below is not identified as redundant.
\begin{verbatim}
type _ t = T1 : int t | T2 : bool t

let f (type a) (x: a t) (y: a s) : unit =
  match (x, y) with
   | (T1, T1) -> ()
   | (T2, T2) -> ()
   | (_,  _)  -> ()
\end{verbatim}

\paragraph{Idris}
Idris~\cite{idris,brady:idris} has very limited checking of
overlapping patterns or redundant patterns.\footnote{Edwin Brady, personal communication}
It does, however, check
coverage, and will use this information in optimisation and code
generation.

\paragraph{ML variants}
Xi.~\cite{dependentxi,deadcodexi,xithesis} shows how to eliminate dead code
for GADT pattern matching -- and dependent pattern matching in general --
for Dependent ML. He has a two-step approach: first add all the missing patterns
using simple-pattern techniques (Section~\ref{sec:related-simple}), and then
prune out redundant clauses by checking when typing constraints are un-satisfiable.
We combine the two steps, but the satisfiability checking is similar.

Dunfield's thesis~\cite[Chapter 4]{dunfieldthesis} presents a coverage
checker for Stardust \cite{stardust}, another ML variant
with refinement and intersection types.  The checker proceeds
in a top-down, left-to-right fashion much like Figure~\ref{fig:algorithm_outline}
and uses type satisfiability to prune redundant cases.

Neither of these works handles guards or laziness.

\subsection{Total Languages}

Total languages like Agda~\cite{norellphd} and Coq~\cite{Coq:manual} must
treat non-exhaustive pattern matches as an \emph{error} (not a warning).
Moreover, they also allow overlapping
patterns and use a variation of Coquand's dependent 
pattern matching~\cite{pmdependent} to report redundant clauses. 
The algorithm works by splitting the context, until the current
neighbourhood matches one of the original clauses. If the current neighbourhood
fails to match all the given clauses, the pattern match is non-exhaustive and a
coverage failure error is issued. If matching is inconclusive though, the
algorithm splits along one of the blocking variables and proceeds recursively
with the resulting neighbourhoods. Finally, the |with|-construct~\cite{norellphd},
first introduced by McBride and McKinna~\cite{viewfromleft}, provides
(pattern) guards in a form that is suitable for total languages. 

The key differences between our work 
and work on dependent pattern matching are the following: (i) because of the possibility of divergence 
we have to take laziness into account; (ii) current presentations of |with|-clauses~\cite{viewfromleft}
do not introduce term-level equality propositions and hence may report inexhaustiveness checking more 
often than necessary, (iii) our approach is easily amenable to external decision procedures that are
proven sound but do not have to return proof witnesses in the proof theory in hand. 


\subsection{Verification Tools}

\paragraph{ESC/Haskell.}
A completely different but more powerful approach can be found in {\em
ESC/Haskell}~\cite{eschaskell} and its successor~\cite{eschaskellnext}.
ESC/Haskell is based on preconditions and contracts, so, it is able to detect
far more defects in programs: pattern matching failures, division by zero, out
of bounds array indexing, etc. Although it is far more expressive than our
approach (e.g. it can verify even some sorting algorithms), it requires
additional work by the programmer through explicit pre/post-conditions.

\paragraph{Catch.}
Another approach that is closer to our work but retains some of the
expressiveness of ESC/Haskell is the tool {\em Catch}~\cite{enoughpats}
Catch generates pre- and
post-conditions that describe the sets of incoming and returned
values of functions (quite similarly to our value abstraction sets). Catch is
based on abstract interpretation over Haskell
terms -- the scope of abstract interpretation in our case is restricted to clauses (and potentially nested patterns). A difference is that Catch operates at the level of Haskell Core, GHC's intermediate language~\cite{hspromoted}. The greatest advantage of this approach is that this language has only 10 data constructors, and hence Catch does not have to handle the more verbose source Haskell AST.
Unfortunately, at the level of Core, the original syntax is lost, leading to
less comprehensive error messages. On top of that, Catch does not take into account type constraints, such as those that arise from GADT pattern matching. Our approach takes them into account and reuses the existing constraint solver infrastructure to discharge them.

\paragraph{Liquid types.}
Liquid types~\cite{liquid,liquidhaskell} is a refinement types extension to
Haskell. Similarly to ESC/Haskell, it could be used to detect redundant,
overlapping, or non-exhaustive patterns, using
an SMT-based version of Coquand's algorithm~\cite{pmdependent}. To take
account of type-level constraints (such as type equalities from GADTs) one
would have to encode them as refinement predicates. The algorithm that we
propose for computing covered, uncovered, and diverging sets would still be
applicable, but would have to emit constraints in the vocabulary of Liquid
types.

% Section 8 (Discussion/Future Work)
%===============================================================================
\section{Discussion and Further Work}\label{discussion}

We presented an algorithm that provides warnings for functions with redundant
or missing patterns. These warnings are accurate, even in the presence of
GADTs, laziness and guards. Our implementation is already available in the GHC repository (branch
@wip/gadtpm@).  Given its power, the algorithm is both modular and simple:
Figure~\ref{fig:algorithm} is really the whole thing, apart from the satisfiability checker.
It provides interesting opportunities for follow-on work, such as smarter reasoning about 
term-level constraints, and exploiting the analysis results for optimised compilation.

\acks

We are grateful to Edwin Brady for explaining Idris' behaviour, and to Jacques
Garrigue and Jacques Le Normand for explaining OCaml's behaviour. We would also
like to thank Nikolaos Papaspyrou for his contribution in the early stages of
this work; and Gabor Greif, Conor McBride, and the ICFP referees
for their helpful feedback.
This work was partially funded by the Flemish Fund for Scientific Research (FWO).

% We recommend abbrvnat bibliography style.

\bibliography{references}{}
\bibliographystyle{abbrvnat}

% The bibliography should be embedded for final submission.

\vspace{0mm} % Just to make it fit in 13 pages :(
%-------------------------------------------------------------------------------
\appendix

\section{Set Size Statistics}\label{pm:performance}

As we discussed in Section~\ref{sec:complexity}, our algorithm has exponential
behaviour in the worst case. Nevertheless, we expect this behaviour to be rare
in practice. To confirm this expectation, we put our implementation to the test by
collecting statistics concerning the size of sets $C$ and $U$ our algorithm
generates for the packages of Section~\ref{sec:evaluation}:
\[
\begin{array}{rrr}
  \textbf{Maximum size of C/U} & \textbf{Pattern Matches} & \textbf{(\%)} \\
  \hline
       1-9 & 8702 & 97.90\% \\
     10-99 &  181 &  2.04\% \\
  100-2813 &    5 &  0.06\% \\
\end{array}
\]
Since there was significant variance in
the results, we divided them into three size groups.
Out of 8888 pattern matches checked in total, almost 98\% of the generated and processed
sets have a size less than 10. In fact, the vast majority (over 95\%) have size 1 or 2.

The percentage of sets with size between 10 and 99 is 
2.04\%. We believe that this percentage is acceptable for types with
many constructors and for pattern matches with many arguments.

Last but not least, we encountered 5 cases (only 0.06\%) with extremely large
sets ($\geq$ 100 elements).  All of them were found in a specific
library\footnote{Library Data.Array.Accelerate.Analysis.Match.} of package
\textit{ad}.
As expected, all these involved pattern matches had the structure of function @f@
from Section~\ref{sec:complexity}:
> data T = A | B | C
> f A A = True
> f B B = True
> f C C = True

Notably, the most extreme example which generated an uncovered set of size
2813, matches against two arguments of type @T@ with 54 data constructors, a
match that gives rise to 3025 different value combinations!

%-------------------------------------------------------------------------------


\end{document}

%                       Revision History
%                       -------- -------
%  Date         Person  Ver.    Change
%  ----         ------  ----    ------

%  2013.06.29   TU      0.1--4  comments on permission/copyright notices

