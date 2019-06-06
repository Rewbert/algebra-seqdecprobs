% -*- latex -*-

\subsection{Example}
\label{subsec:example}

%if false
module examples where

\begin{code}
open import core.traj
open import core.seqdecproc
open import core.seqdecprob hiding (Policy; PolicySeq)
open import Data.Nat hiding (_<_)
open import Agda.Builtin.Nat using (_<_)
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Data.Bool
\end{code}

%endif

Let us consider a sequential decision process where the state space is a one dimensional coordinate system represented by natural numbers.
%
\begin{code}
oned-state  :  Set
oned-state  =  ℕ
\end{code}

%if false
\begin{code}
distance : ℕ → ℕ → ℕ    -- distance m n = abs (m-n)  informally
distance zero zero       = 0
distance zero (suc m)    = 1 + distance zero m
distance (suc n) zero    = 1 + distance n zero
distance (suc n) (suc m) = distance n m
\end{code}
%endif

%
Seeing how the state space are the natural numbers we emphasize that the coordinate system has only positive coordinates.
%
In any given state, generally, we can choose to either increment, decrement or do nothing to the state.
%
In the edge case where the state is |0| we can not decrement the state.
%
We can encode this control as a type family in Agda.
%
\begin{code}
data oned-control : oned-state -> Set where
  Right  : {n : oned-state} -> oned-control n
  Stay   : {n : oned-state} -> oned-control n
  Left   : {n : oned-state} -> oned-control (suc n)
\end{code}
%
We implement the step function by pattern matching on the control.
%
\TODO{spellcheck recognises}
In the case of the |Left| control Agda recognises that the state must be a sucessor.
%
We increment or decrement the state accordingly and leave it unchanged for the |Stay| control.
%
\begin{code}
oned-step  :  (x : oned-state) -> oned-control x -> oned-state
oned-step x        Right  = suc x
oned-step x        Stay   = x
oned-step (suc x)  Left   = x
\end{code}
%
We define a policy to be a function that given a state select a control.
%
The policies right, stay and tryleft are all policies of this kind.
%
tryleft is special in the sense that if the state is zero it will do nothing, as it can not go left.
%
\TODO{Put policy in record}
\begin{code}
oned-Policy = (x : oned-state) -> oned-control x

right stay tryleft : oned-Policy
right    _        = Right
stay     _        = Stay
tryleft  zero     = Stay
tryleft  (suc s)  = Left
\end{code}
%
We can parameterise a policy over a coordinate and define a policy that will select controls that moves the system towards this coordinate.
%
\begin{code}
towards : ℕ -> oned-Policy
towards goal n with compare n goal
... | less _ _     = Right
... | equal _      = Stay
... | greater _ _  = Left
\end{code}
%
With the three components state, control and step, we can instantiate a sequential decision process.
%
\begin{code}
oned-system  :  SDProc
oned-system  =  SDP oned-state oned-control oned-step
\end{code}
%
A policy sequence is now just a vector of policies.
%
\begin{code}
pseq : PolicySeq (#st oned-system) (#c oned-system) 5
pseq = tryleft ∷ tryleft ∷ right ∷ stay ∷ right ∷ []
\end{code}
%
We can evaluate the system using this sequence, starting from different points.
%
We can use |≡| and |refl| to assert that the system behaves as intended.
%\TODO{Maybe explain briefly what refl and ≡ are?}
%
\begin{code}
test1 : trajectory oned-system pseq 0 ≡  0 ∷ 0 ∷ 1 ∷
                                         1 ∷ 2 ∷ []
test1 = refl

test2 : trajectory oned-system pseq 5 ≡  4 ∷ 3 ∷ 4 ∷
                                         4 ∷ 5 ∷ []
test2 = refl
\end{code}
%
We can use the clever policy to steer the process towards a goal.
%
\begin{code}
test3 :  trajectory oned-system (replicate (towards 5)) 2 ≡
          3 ∷ 4 ∷ 5 ∷ 5 ∷ 5 ∷ []
test3 = refl
\end{code}

%
To turn a process into a problem we need to introduce a notion of a goal, described by a |reward| function.
%
For our example we define the reward function to be parameterised over a target coordinate.
%
The reward function could then reward a proposed step based on how close to the target it lands.
%
\begin{code}
oned-reward  :  oned-state
             →  (x : oned-state) → oned-control x
             →  oned-state → ℕ
oned-reward target x₀ y x₁
  = if distance target x₁ < distance target x₀
    then 2
    else (if distance target x₀ < distance target x₁
          then 0
          else 1)
\end{code}
%
We can redefine the sequential decision process above to be a sequential decision problem simply by instantiating the |SDProb| record.
%
\begin{code}
problem : oned-state -> SDProblem
problem target
  = SDProb  oned-state  oned-control
            oned-step   (oned-reward target)
\end{code}

%\TODO{Example ``run'' would be instructive}
