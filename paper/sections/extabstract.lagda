% -*- Latex -*-
\section{Introduction}
\label{sec:introduction}
Sequential decision processes and problems are a well established concept in decision theory, with the Bellman equation \cite{Bellman1957} as a popular choice for describing them.
%
Botta et al \cite{brady2013idris} have formalised the notion of such problems in Idris. %, a general purpose programming language with dependent types.
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

\paragraph{Examples:}
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
>  game = p²' ⊎SDPT (embed p³)

%
These combinators, and more, make up an \emph{Algebra of SDPs}.%Sequential Decision Processes
%

\section{Sequential Decision Problems}
\label{sec:seqdecproc}
%
First, we formalise the notion of a Sequential Decision \emph{Process} in Agda.
%
A process always has a \emph{state}, and depending on what that state is there are different \emph{controls} that describe what actions are possible in that state.
%
The last component of a sequential decision process is a function |step| that when applied to a state and a control for that state returns the next state.
%
%if False
\begin{code}
module extabstract where

open import Data.Nat
open import Data.Product
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import core.traj

open import examples using (oned-state; oned-control; oned-step; oned-system; tryleft; stay; right)
open import core.seqdecproc -- using (SDProc; #st_; #sf_)
open import combinators using (Con; Step)
open import policycombinators using (_×P_)

Val = ℕ
\end{code}
%endif
%
To better see the type structure we introduce a type synonym for the family of controls depending on a state:
%
\begin{spec}
Con : Set → Set₁
Con S = S → Set
\end{spec}
%
and for the the type of step functions defined in terms of a state and a family of controls on that state:
%
>Step : (S : Set) -> Con S -> Set
>Step S C = (s : S) -> C s -> S
%
With these in place we define a record type for SDPs:% Sequential Decision Processes
\savecolumns
>record SDProc : Set1 where
>  constructor SDP
>  field    State    : Set
>           Control  : Con State
>           step     : Step State Control
%
We can extend this idea of a sequential decision \emph{process} to that of a \emph{problem} by adding an additional field |reward|.
%
\restorecolumns
>           reward   :  (x : State) -> Control x -> Val
%
where |Val| is often |ℝ|.
%
From the type we conclude that the reward puts a value on the steps taken by the step function, based on the state transition and the control used.
%
The problem becomes that of finding the sequence of controls that produces the highest sum of rewards.
%
Or, in more realistic settings with uncertainty (which can be modelled by a monadic step function), finding a sequence of \emph{policies} which maximises the |expected| reward.
%
The system presented here aims at describing finite horizon problems, meaning that the sum of rewards is over a finite list.
%
Furthermore, rewards are usually discounted the as time passes.
%
One action |now| is worth more than the same action a few steps later.
%
Rewards, and problems, are not the focus of this abstract but are mentioned for completeness.

A policy is a function from states to controls:
%
>Policy : (S : Set) -> Con S -> Set
>Policy S C = (s : S) → C s
%
Given a list of policies to apply, one for each time step, we can compute the trajectory of a process from a starting state.
%
Here the |#st| and |#sf| functions extract the state and step component from the |SDProc| respectively.
%
%include core/traj.lagda
%
As an example of a trajectory computation we return to the one dimensional process |oned-system| (called just |p| in the intro) and an example policy sequence |pseq|.
%
Ideally |pseq| is the result of an optimization computed using Bellmans backwards induction.
%
Here we just illustrate one trajectory:
%
\begin{code}
pseq = tryleft ∷ tryleft ∷ right ∷ stay ∷ right ∷ []
test1 :  trajectory oned-system pseq 0 ≡  0 ∷ 0 ∷ 1 ∷ 1 ∷ 2 ∷ []
test1 = refl
\end{code}
%
In an applied setting many trajectories would be computed to explore the system behaviour.
%
%We use a sequence of policies rather than a constant policy as the policy is something of a strategy.
%
%As a process progresses and different states are inhabited one might wish to alter his or her strategy.
%
This brief example is fully presented in an accompanying technical report \cite{AlgSDPreport}.
%

%
In this abstract we focus on non-monadic, time-independent, sequential decision processes, but the algebra extends nicely to the more general case.
%
\section{The Product Combinator}
\label{sec:aproductcombinator}
%
To compute |p²| we need to define a \emph{product} combinator for SDPs.
%
We illustrate what this combinator does in Figure \ref{images:product}.
%
\begin{figure}
\centering
\includegraphics[scale=0.7]{images/product.png}
\caption{The product process holds components of both states and applies the step function to both components simultaneously. Each component of the next state has two incoming arrows as the policy that computes the control that is used has access to both components of the previous state.}
\label{images:product}
\end{figure}
%
The state of the product of two processes is the cartesian product of the two separate states.
%

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
Given two step functions we can define a new step function for the product process by returning the pair computed by applying the individual step functions to the corresponding components of the input.
%
\begin{code}
_×sf_  :   {S₁ S₂ : Set} {C₁ : Con S₁} {C₂ : Con S₂}
       ->  Step S₁ C₁ -> Step S₂ C₂
       ->  Step (S₁ × S₂) (C₁ ×C C₂)
(sf₁ ×sf sf₂) (s₁ , s₂) (c₁ , c₂) = (sf₁ s₁ c₁ , sf₂ s₂ c₂)
\end{code}
%
Finally, we can compute the product of two sequential decision processes by applying the combinators componentwise.
%
\begin{code}
_×SDP_ : SDProc → SDProc → SDProc
(SDP S₁ C₁ sf₁) ×SDP (SDP S₂ C₂ sf₂)
  = SDP (S₁ × S₂) (C₁ ×C C₂) (sf₁ ×sf sf₂)
\end{code}

%
To illustrate how the combinator works we apply it to the system (|oned-system|) mentioned previously.
%
\begin{code}
twod-system = oned-system ×SDP oned-system
\end{code}
%
Now |twod-system| is a process of two dimensions rather than one, as illustrated by the type of |test2|.
%
\begin{code}
twodsequence = zipWith _×P_ pseq pseq
test2  :  trajectory twod-system twodsequence (0 , 5)
       ≡  (0 , 4) ∷ (0 , 3) ∷ (1 , 4) ∷  (1 , 4) ∷ (2 , 5) ∷ []
test2 = refl
\end{code}
%

\section{Wrapping up}

In the technical report \cite{AlgSDPreport} we present more combinators for time dependent and time independent processes and policies.
%
We implement the example of a coordinate system described above, and make it even more precise as a time dependent process.
%
Future work includes generalising to monadic SDPs and applying our combinators to the green house gas emission problem \cite{esd-2017-86}.

We thank the anonymous reviewers for their helpful comments and the Agda developers for a great tool!