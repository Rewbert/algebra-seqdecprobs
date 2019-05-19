% -*- Latex -*.
\section{Introduction}
\label{sec:introduction}
% (explain title) - zoom in from general to specific - check
% identify a gap (some ref. to earlier work and explain why something is lacking)
% fill the gap! - check (i think)
% contributions of this paper / outline - check
% Zoom in from broad perspective on the field towards more specific questions in the current paper.
% TODO cite Bellman
Sequential decision processes and problems are a well established concept in decision theory, with the Bellman equation \cite{Bellman1957} as a popular choice for describing them.
%
Botta et al \cite{brady2013idris} have formalised the notion of such problems in Idris, a general purpose programming language with dependent types.
%
Using dependent types to bridge the gap between description and implementation of complex systems, for purposes of simulation, has been shown to be a good choice \cite{ionescujansson2013DTPinSciComp}.
%
They have illustrated how to use their formulation to model e.g.\ climate impact research \cite{esd-2017-86}, a very relevant problem today.
%
% Modeling climate impact is challenging because it involves very dynamic processes with many unknown variables.
%TODO perhaps remove or rewrite the above sentence. Yes perhaps, i tried to introduce a sentence that motivated why combining simpler problems is desired. Might be clear enough without it.
Evidence based policy making (when dealing with climate change or other global systems challenges), requires computing policies which are verified to be correct.
%**TODO "requires" is perhaps a bit too strong
There are several possible notions of ``correctness'' for a policy: computing feasible system trajectories through a state space, avoiding ``bad'' states, or even computing optimal policys.
%
The concepts of feasibility and avoidability have been formalised and presented in \citet{botta_jansson_ionescu_2017_avoidability}.
%
Although motivated by the complexity of modelling in climate impact research, we focus on simpler examples of sequential decision processes and how to combine them.

Assume that we have a process |p : SDProc| that models something moving through a 1-D coordinate system with a natural number as the state and |+1|, |0|, and |-1| as actions.
%
If the circumstances change and we need to model how something moves in a 2-D coordinate system, it would be convenient if we could reuse the one dimensional system and get the desired system for free.
%
We seek a combinator |_×SDP_ : SDProc → SDProc → SDProc| such that
%
\begin{code}
  p² = p ×SDP p
\end{code}

Both |p| and |p²| use a fixed state space, but we can also handle time dependent processes.
%
Assume |p' : SDProcT| is similar to |p| but time dependent: not all states are available at all times, meaning |p'| is more restricted in the moves it can make.
%
If we want to turn this into a process that can also move around in a second dimension, we want to be able to reuse both |p'| and |p|.
%
We can use a combinator |_×SDPT_ : SDProcT → SDProcT → SDProcT| together with the trivial embedding of a time independent, as a time dependent, process |embed : SDProc → SDProcT|.
%
\begin{code}
  p²' = p' ×SDPT (embed p)
\end{code}

As a last example consider the case where we want a process that moves either in a 3-D coordinate system |p³ = p² ×SDP p| or in |p²'|.
%
You could think of this as choosing a map in a game.
%
Then we would want a combinator |_⊎SDPT_ : SDProcT → SDProcT → SDProcT| such that
%
\begin{code}
  game = p²' ⊎SDPT (embed p₃)
\end{code}

%
These combinators, and more, make up an \emph{Algebra of Sequential Decision Processes}.
%
% \TODO{If this is indeed a pearl, we need to be clearer about this, and consistent.}
Parts of this algebra is investigated in this pearl.
%

\subsection{Contributions}
\label{subsec:contributions}
%
In this text we implement a small library of combinators for sequential decision processes.
%
We give examples where we use the combinators mentioned above and discuss the properties of the resulting processes.
%
In section \ref{sec:timedependentcase} we define time dependent processes and follow up by reimplementing a previously seen example, where we can now be more fine grained about what we are modeling.
%
Then we redefine the previously implemented combinators in terms of these new processes.
%
As it turns out, this is not entirely straightforward.
%

%
Lastly we present combinators for policies and policy sequences.
%
This is the final piece that lets us create and run processes without writing any new code, but only by reusing code for existing processes.
%
