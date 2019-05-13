% -*-Latex-*-
\section{Introduction}
\label{section:introduction}

\subsection{About this work}

In this article we apply the framework for specifying and solving
sequential decision problems (SDPs) presented in \cite{botta+al2014a} to
understand the impact of uncertainty on optimal greenhouse gas (GHG)
emission policies.
%
Specifically, we study the impact of
%
\begin{enumerate}
\item Uncertainty about the implementability of decisions on GHG
  emission reductions,
\item uncertainty about the availability of efficient technologies for
  reducing GHG emissions,
\item uncertainty about the implications of exceeding a critical
  threshold of cumulated GHG emissions.
\end{enumerate}
%
The work is also an application of the computational theory of policy
advice and avoidability proposed in \cite{botta+al2016}.
%
The theory supports a seamless approach towards accounting for
different kinds of uncertainties and makes it possible to rigorously
assess the logical consequences, among others, the risks, entailed by
the implementation of optimal policies.
%
We explain what policies are and what it means for a policy sequence
to be optimal in section \ref{subsection:policies}.


\subsection{Sequential decision problems and climate change}

In many decision problems in the context of climate change, decisions
have to be taken \emph{sequentially}: emission rights are issued year
after year, emission reduction plans and measures are iteratively
revised and updated at certain (perhaps irregular) points in time,
etc.

In its fourth Assessment Report \cite{ipcc2007a}, the Intergovernmental
Panel on Climate Change (IPCC) has pointed out that responding to
climate change involves \enquote{an iterative risk management process
  that includes both mitigation and adaptation, taking into account
  actual and avoided climate change damages, co-benefits,
  sustainability, equity and attitudes to risk.}

%**TODO: Too many short paragraphs follow - some may be joined together.

The paradigmatic example of iterative SDPs in the context of climate
change is that of controlling GHG emissions.
%
In GHG emission control problems, a decision maker or a finite number
of decision makers (countries) have to select an emission level or,
equivalently, a level of emission abatement (reduction) with respect
to some reference emissions.
%
The idea is that the selected abatement level is then implemented,
perhaps with some deviations, over a certain period of time. After
that period another decision is taken for the next time period.

Implementing abatements implies both costs and benefits.
%
These are typically affected by different kinds of uncertainties but
the idea is that, for a specific decision maker, a significant part of
the benefits come from avoided damages from climate change.
%
Avoided damages essentially depend on the overall abatements: higher
global abatements lead to less damages and thus higher benefits.
%
In contrast, costs are very much dependent on the abatement level
implemented by the specific decision maker.
%
Here, higher emission reductions cost more than moderate emission
reductions.

It turns out that, when considering a single decision step and for
fairly general and realistic assumptions on how costs and benefits
depend on abatement levels, the highest global benefits are obtained
if all decision makers reduce emissions by certain \enquote{optimal}
amounts \citep{finus+al2003,helm2003,heitzig+al2011}.

In this situation, however, many (if not all) decision makers
typically face a free-ride option: they could do even better if they
themselves would not implement any emission reduction (or, perhaps, if
they would implement less reductions) but all the others would still
comply with their quotas.
%
It goes without saying that if all players fail to comply with their
optimal emission reduction quotas, the overall outcome will be
unsatisfactory for all or most players.

This situation is often referred to as an instance of the
\enquote{Tragedy of the Commons} \cite{hardin1968} and has motivated a
large body of research, among others, on coalition formation and on
the design of mechanisms to deter free-riding.
%
These studies are naturally informed by game-theoretical approaches
and focus on the non-parametric nature of decision making.
%
The sequentiality of the underlying decision process and the temporal
dimension of decision making are traded for analytic tractability.
%
For a survey, see \cite{heitzig+al2011}.

%**TODO: "traded in favor of ...": I think there is something wrong the grammar
%**DONE: changed to "traded for ..."

Another avenue of research focuses on the investigation of optimal
global emission paths or, as we shall see in section
\ref{subsection:policies}, of optimal sequences of global emission
policies.
%
Here, the core question is how uncertain future developments,
typically, the introduction of new technologies or the crossing of
climate stability thresholds, shall inform current decisions.
%
In a nutshell, the problems here are \emph{when} global emissions
should be reduced and by \emph{how much} given the uncertainties that
affect both our understanding of the earth system and the
socio-economic consequences of implementing emission reductions.

In these kinds of studies, the presence of multiple decision makers
with possibly conflicting interests and the question of \emph{how}
emission reductions can actually be implemented is neglected.
%
This makes it possible to apply control theoretical approaches and to
fully account for the temporal dimension of sequential emission
games.
%
This is also the approach followed in this work.
%
To the best of our knowledge, no theory is currently available for
tackling the problem of computing optimal emission policies for
individual countries as a (mixed sequential and simultaneous)
coordination game with a finite number of decision makers, over a finite
(but not necessarily known) number of decision steps and under different
sources of uncertainty.
%
For a survey of SDPs under uncertainty in climate change see
\cite{ParsonKarwat2011}, \cite{Peterson2006} and references therein.

\subsection{Stylized sequential emission problems}

One can try to understand the impact of uncertainties on optimal
emission policies for a specific, real (or, more likely, realistic)
emission problem.
%
This requires, among others, specifying an integrated climate-economy
assessment model or, as done in \cite{webster2008}, some tabulated
version of the model underlying the problem.
%
The approach supports drawing conclusions which are specific for the
problem under investigation and is what is typically done in applied
policy advice.
%
On the other hand, studying a specific, realistic problem makes it
difficult to draw general conclusions and is well beyond the scope of
this work.

An alternative approach towards understanding the impacts of
uncertainties on optimal policies is to study a \enquote{stylized}
emission problem.
%
A stylized emission problem does not attempt at being realistic.
%
Instead, it tries to capture the essential features of a whole class
of problems and supports general instead of specific conclusions.
%
This is the approach followed in this paper.

\subsection{Notation}
\label{subsection:notation}

In section \ref{section:optimal_policies} we apply the theory for
specifying and solving SDPs from \cite{botta+al2014a,botta+al2016} to
the stylized emission problem from section \ref{section:stylized_sep}.
%
The theory is based on the notion of \emph{monadic} dynamical systems
originally introduced in \cite{ionescu2009}. In this context,
monads allows one to treat deterministic, non-deterministic, stochastic,
fuzzy, etc. uncertainty with a seamless approach: the differences are
captured by a single problem parameter and all computations are generic
with respect to this parameter.
%
In a nutshell, the theory is a dependently typed formalization of
dynamic programming \citep{bellman1957}. The formalization language is
Idris, see \cite{idristutorial}. For a discussion on why functional,
dependently typed languages are the first choice for implementing such
formalizations, see \cite{botta+al2016}.

Because the theory is dependently typed, some familiarity with a
functional, dependently typed notation is mandatory to apply it to a
specific decision problem. In this paper, we do not assume that our
readership is familiar with dependent types and functional
languages. Thus, in sections \ref{section:seps} to
\ref{section:conclusions} , we have restricted the formalism to the
barely minimum. A simplified summary of the \cite{botta+al2016} theory
is provided in appendix \ref{appendix:summary}.

Still, a number of formulas appear in sections \ref{section:seps} to
\ref{section:conclusions}. In the rest of this section we introduce the
notation used in these formulas. This is a blend of standard
mathematical notation and of standard (Haskell, Idris, Agda, etc.)
functional programming notation.

Thus, for instance, in section \ref{section:seps}, we write $Technology
= \{Available, Unavailable\}$ to posit that $Technology$ is a set that
consists of two elements: $Avaialable$ and $Unavailable$. This is plain
set comprehension as in $Bool = \{False, True\}$, $A = \{7,4,2\}$ or
$Even = \{2 * n \mid n \in \mathbb{N}\}$.

Further, in section \ref{section:seps}, we write |State : (t : Nat) ->
Type| to posit that \enquote{|State t| denotes the set of states the
  decision maker can observe at the |t|-th decision step}. This is now
standard Idris notation. Idris (and Haskell, Agda) follows the usual
meaning of parentheses in mathematics: to enclose a sub-expression to
resolve operator precedence. The special notation $f(a)$ for the value
of a function $f : A \to B$ at $a \in A$ (very much used in physics and
engineering) uses parentheses in a non-standard way.

Another possible source of confusion is the signature (type) of the
function |State|. Its domain are values of type |Nat| that is, natural
numbers. But its co-domain are values of type |Type|! Thus, for instance
a legal definition of |State| could be

\small
< State t = Bool
\normalsize

\noindent
which posits that |State| is the constant function that returns the type
|Bool| for every |t|. Being able to implement functions that return
types is a key feature of dependently typed languages. Among others, it
allows one to encode first-order logic propositions as types. Thus, for
instance

\small
< BoundedBy : Nat -> List Nat -> Type
< BoundedBy n ms = All (\ m => m `LTE` n) ms
\normalsize

\noindent
is a legal function definition and a value of type |BoundedBy 5 xs| is
equivalent to a logical proof that all elements of |xs| are smaller or
equal to |5|. Perhaps unexpectedly, the type of |m `LTE` n| on the right
hand side of the definition of |BoundedBy| is |Type|, not |Bool|. This
also the type of |All (\ m => m `LTE` n) ms| as can be seen from the
declaration of |BoundedBy|. Thus, |m `LTE` n| and |All (\ m => m `LTE`
n) ms| encode logical propositions as types: they are propositional
types. Here, |LTE| and |All| are standard data types defined in the
Idris libraries. Being able to encode logical propositions as types is
crucial for formulating program specifications, that is, properties that
a program must satisfy to be correct. Thus, for example, a program

\small
< sqrt : Double -> Double
\normalsize

\noindent
that is meant to compute the square root of a double precision floating
point number might be required to fulfill

\small
< sqrtSpec : (x : Double) -> 0 `LTE` x -> (sqrt x) * (sqrt x) = x
\normalsize

\noindent
The specification |sqrtSpec| is logically equivalent to the proposition
``for all |x| of type |Double|, if |x| is non-negative then the square
of |sqrt x| is equal to |x|''\footnote{A more realistic specification
  would require that the square of |sqrt x| is equal to |x| up to
  round-off errors but we do not insist on these details here.}. As
above, |0 `LTE` x| and |(sqrt x) * (sqrt x) = x| are values of type
|Type|, in contrast to |0 <= x| and |(sqrt x) * (sqrt x) == x| which are
Boolean values. They encode properties that depend on a specific value
|x| that is, they are dependently typed types.

The types of |sqrt| and |sqrtSpec| formulate a well defined, unambiguous
task for the programmer. This is solved by providing implementations of
|sqrt| and |sqrtSpec| that are syntactically correct and total. In this
case, the implementation of |sqrt| is said to be verified or,
equivalently, machine checked. Notice that totality plays a crucial role
in this context. Only total implementations of |sqrt| and |sqrtSpec| are
logically equivalent to the proposition ``for all |x| of type |Double|,
if |x| is non-negative then the square of |sqrt x| is equal to |x|''.

Because |sqrtSpec| represents a property of |sqrt|, implementations of
|sqrtSpec| will depend on a specific implementation of |sqrt|: one
typically starts by implementing |sqrt| and then tries to prove that
that implementation is correct that is, to implement |sqrtSpec|.
Implementations of |sqrtSpec| are typically derived from
pencil-and-paper proofs (that |sqrt| fulfills the property encoded in
the type of |sqrtSpec|) but dependently typed languages provides a lot
of support to programmers: the Idris system can ``fill in'' parts of the
implementation of |sqrtSpec| automatically.

Dependent types are also the key for expressing (perhaps
non-implementable) modeling assumptions or conjectures and for
formalizing domain-specific notions precisely. In sections
\ref{section:seps} to \ref{section:conclusions} we will not make
explicit usage of propositional types. But propositional types are at
the core of the theory presented in \cite{botta+al2014a,botta+al2016}
and are extensively used there and in appendix \ref{appendix:summary}.

Another perhaps unfamiliar aspect of functional notations is currying.
In mathematics, a function of $n > 1$ arguments is often implicitly
converted to a function that takes as a single argument one $n-$tuple.
In Idris we instead use nested function application. Thus, if |g| has
type |X -> (Y -> Z)| or simply |X -> Y -> Z| we write |(g x) y| (or
simply |g x y| because function application is left-associative) to
denote the value (of type |Z|) of |g x| (a function of type |Y -> Z|) at
|y : Y|\footnote{The idea that functions of more than one variable can
  always be written as functions of just one variable (that return
  functions as result) was originally proposed in
  \cite{schoenfinkel1924} and popularized by Haskell B.\ \cite{curry1958}.
  %
  The operation is since the referred to as \emph{currying}. Its
  inverse is called \emph{uncurrying}.}.

Notice that even though we do not use propositional types in
\ref{section:seps} to \ref{section:conclusions}, most functions there
are dependently typed. Thus, for instance, in the signature of |Control|
at page 5, the type of the second argument, |State t|, depends on the
value of the first argument, |t|. We say that |Control| is dependently
typed \citep{norell2007thesis,idristutorial,brady2016}.

Finally, the \cite{botta+al2014a,botta+al2016} theory applied in this
paper is available in the \texttt{SequentialDecisionProblems} component
of \cite{botta2016-}. This is a git repository and it is publicly
available.


\subsection{Outline}

In the next section we introduce sequential emission problems and
explain what it means for sequences of emission policies to be
optimal.
%
We discuss the most important differences between deterministic
(certain) problems and emission problems under uncertainty.
%
In section \ref{section:logical_consequences} we discuss some
important traits of decision making under uncertainty.
%
The discussion is meant to prepare the specification of the stylized
emission problem presented in section \ref{section:stylized_sep}.
%
In section \ref{section:optimal_policies} we study the impact of the
uncertainties (1)--(3) on optimal policy sequences for our stylized
problem.
%
We draw preliminary conclusions and outline future work in section
\ref{section:conclusions}.
