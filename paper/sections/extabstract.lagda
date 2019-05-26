% -*- Latex -*-
\section{Introduction}
\label{sec:introduction}
Sequential decision processes and problems are a well established concept in decision theory, with the Bellman equation \cite{Bellman1957} as a popular choice for describing them.
%
Botta et al \cite{brady2013idris} have formalised the notion of such problems in Idris, a general purpose programming language with dependent types.
%
Using dependent types to bridge the gap between description and implementation of complex systems, for purposes of simulation, has been shown to be a good choice \cite{ionescujansson2013DTPinSciComp}.
%
They have illustrated how to use their formulation to model e.g.\ climate impact research \cite{esd-2017-86}, a very relevant problem today.
%

%
Evidence based policy making (when dealing with climate change or other global systems challenges), requires computing policies which are verified to be correct.
%
There are several possible notions of ``correctness'' for a policy: computing feasible system trajectories through a state space, avoiding ``bad'' states, or even computing optimal policys.
%
The concepts of feasibility and avoidability have been formalised and presented in \citet{botta_jansson_ionescu_2017_avoidability}.
%

%
Although motivated by the complexity of modelling in climate impact research, we focus on simpler examples of sequential decision processes and how to combine them.
%

Assume that we have a process |p : SDProc| that models something moving through a 1-D coordinate system with a natural number as the state and |+1|, |0|, and |-1| as actions.
%
If the circumstances change and we need to model how something moves in a 2-D coordinate system, it would be convenient if we could reuse the one dimensional system and get the desired system for free.
%
We seek a combinator |_×SDP_ : SDProc → SDProc → SDProc| such that
%
>  p² = p ×SDP p

Both |p| and |p²| use a fixed state space, but we can also handle time dependent processes.
%
Assume |p' : SDProcT| is similar to |p| but time dependent: not all states are available at all times, meaning |p'| is more restricted in the moves it can make.
%
If we want to turn this into a process that can also move around in a second dimension, we want to be able to reuse both |p'| and |p|.
%
We can use a combinator |_×SDPT_ : SDProcT → SDProcT → SDProcT| together with the trivial embedding of a time independent, as a time dependent, process |embed : SDProc → SDProcT|.
%
>  p²' = p' ×SDPT (embed p)

As a last example consider the case where we want a process that moves either in a 3-D coordinate system |p³ = p² ×SDP p| or in |p²'|.
%
You could think of this as choosing a map in a game.
%
Then we would want a combinator |_⊎SDPT_ : SDProcT → SDProcT → SDProcT| such that
%
>  game = p²' ⊎SDPT (embed p₃)

%
These combinators, and more, make up an \emph{Algebra of Sequential Decision Processes}.
%

\section{Sequential Decision Problems}
\label{sec:seqdecproc}
%
First, we formalise the notion of a Sequential Decision \emph{Process} in Agda.
%
A process always has a |state|, and depending on what that state is there are different |controls| that describe what actions are possible in that state.
%
The last component of a sequential decision process is a function |step| that when applied to a state and a control for that state returns the next state.
%
%if False
\begin{code}
module extabstract where

open import Data.Nat
open import Data.Product

\end{code}
%endif
%
To better see the type structure we introduce a type synonym for the family of controls depending on a state:
%
\begin{code}
Con : Set → Set₁
Con S = S → Set
\end{code}
%
and for the the type of step functions defined in terms of a state and a family of controls on that state:
%
\begin{code}
Step : (S : Set) -> Con S -> Set
Step S C = (s : S) -> C s -> S
\end{code}
%
With these in place we define a record type for Sequential Decision Processes:
\begin{code}
record SDProc : Set1 where
  constructor SDP
  field
    State    : Set
    Control  : Con State
    step     : Step State Control
\end{code}
%
We can extend this idea of a sequential decision |process| to that of a |problem| by adding an additional field |reward|.
%
\begin{code}
-- ...
    reward   :  (x : State) -> Control x -> State -> Val
\end{code}
%
From the type we conclude that the reward puts a value on the steps taken by the step function.
%
The problem becomes that of finding the sequence of controls that produces the highest sum of rewards.
%
Or, in more realistic settings with uncertainty (which can be modelled by a monadic step function), finding a sequence of \emph{policies} which maximises the expected reward.
%
A policy is a function from states to controls:
%
\begin{code}
Policy : (S : Set) -> Con S -> Set
Policy S C = (s : S) → C s
\end{code}
%
\TODO{insert trajectory computation from policy sequence}


In this abstract we focus on non-monadic, time-independent, sequential decision processes, but the algebra extends nicely to the more general case.

\section{The Product Combinator}
\label{sec:aproductcombinator}
%
To compute |p²| we need to define a |product| combinator for SDPs.
%
The state of the product of two processes is the product of the two separate states.
%

%
The other components, the |Control| and the function |step| must be described and combined more thoroughly.
%
% We needed a new name: |Pred|icate indicates that we only care about the resulting |Set| being empty or not, but in reality we really care about the control sets. I have changed (in this file) to |Con|.
%
Given two control families, we can compute the control family for pairs of states.
%
The inhabitants (the controls) of each family member are pairs of controls for the two state components.
%
\begin{code}
_×C_  :  {S₁ S₂ : Set} ->
         Con S₁ -> Con S₂ -> Con (S₁ × S₂)
(C₁ ×C C₂) (s₁ , s₂) = C₁ s₁ × C₂ s₂
\end{code}
%
%TODO Maybe insert conor mcbride discussion here - not for the extabstract
%
Next we want to compute the product of two such step functions.
%
Given two step functions we can define a new step function by returning the pair computed by applying the individual step functions to the corresponding components of the input.
%
\begin{code}
_×sf_  :  {S₁ S₂ : Set} ->
          {C₁ : Con S₁} {C₂ : Con S₂} ->
          Step S₁ C₁ -> Step S₂ C₂ ->
          Step (S₁ × S₂) (C₁ ×C C₂)
(sf₁ ×sf sf₂) (s₁ , s₂) (c₁ , c₂) = (sf₁ s₁ c₁ , sf₂ s₂ c₂)
\end{code}
%
Now we have combinators for each of the individual components.
%
We can compute the product of two sequential decision processes by applying the combinators componentwise.
%
\begin{code}
_×SDP_ : SDProc → SDProc → SDProc
(SDP S₁ C₁ sf₁) ×SDP (SDP S₂ C₂ sf₂)
  = SDP (S₁ × S₂) (C₁ ×C C₂) (sf₁ ×sf sf₂)
\end{code}
