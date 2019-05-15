% -*- Latex -*.
\section{Introduction}
\label{sec:introduction}
% (explain title) - zoom in from general to specific
% identify a gap (some ref. to earlier work and explain why something is lacking)
% fill the gap!
% contributions of this paper / outline
%
Sequential decision processes and problems are a well established concept in decision theory.
%
Botta et al. have formalised the notion of such problems in Idris \cite{brady2013idris}, a general purpose programming language with dependent types.
%
They have illustrated how to use their formulation to model e.g climate impact research \cite{esd-2017-86}.
%
Modeling e.g the climate or climate impact is not a trivial task, as such entities are very dynamic processes with many unknown variables.
%

%
We give a simpler example of a sequential decision process.
%
Assume that we have a process |p : SDProc| that models something moving through a one dimensional coordinate system.
%
If the circumstances changed and we now need to model how something moves in a two dimensional coordinate system, it would be convenient if we could reuse the one dimensional system and get the desired system for free.
%
We seek a combinator |_×SDP_| such that
> p² = p ×SDP p

%
A slightly more interesting example is a process |p'| that issimilar to |p|, but it is time dependent.
%
This time dependent process captures the notion that not all states are available at all times, meaning it is restricted in the moves it can take.
%
If we want to turn this into a process that can also move freely in a second dimension, we want to be able to reuse both |p'| and |p| and do something like
> p²' = p' ×SDP (embed p)
%

%
As a last example consider the case where we want a process that moves in a three dimensional coordinate system
> p³ = p² ×SDP p
or in
> p²'
%
This could perhaps model something like choosing a map in a game.
%
Then we would want a process |_⊎SDP_| such that
> p²'+p³ = p²' ⊎SDP (embed p₃)
%

%
These combinators and more make up parts of an |Algebra of Sequential Decision Processes|.
%
Parts of this algebra is investigated in this pearl.
%


\subsection{Contributions}
\label{subsec:contributions}
%
In this pearl we implement a small library of combinators for sequential decision processes.
%
We give an example where we use the combinator mentioned above and discuss what properties the resulting process has.
%
In section \ref{sec:timedependentcase} we define time dependent processes and follow up by redefining the combinators to work with these new processes.
%
It turns out that it is not entirely straight forward to do this, and we discuss why this is the case.
%
We then move on to illustrating how we can use time dependent processes to reimplement the example of the time independent case, but where we are more fine grained about what the process actually models. % i mean here that the state is more 'reasonable'.
%
% om vi har med policy combinators, nämn dem här i suppose.
%
