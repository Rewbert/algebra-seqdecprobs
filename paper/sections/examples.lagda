% -*- latex -*-

\section{Examples}
\label{sec:examples}


%if false
module examples where

\begin{code}
open import core.seqdecproc
open import core.seqdecprob hiding (Policy; PolicySeq)
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality
\end{code}

%endif

As an example, let us consider a sequential decision process where the state space is a one dimensional coordinate system represented by natural numbers.
%

\begin{code}
oned-state  :  Set
oned-state  =  ℕ
\end{code}

%
There are generally three available controls, taking a step to the left, staying or taking a step to the right.
%
Here taking a step to the left means subtracting one from the coordinate, stay means not changing it at all and taking a step to the right means incrementing it by one.
%

\begin{code}
data SAction : Set where
  SL  : SAction -- left
  SS  : SAction -- stay
  SR  : SAction -- right
\end{code}

%
However, there is an edge case.
%
When the state is zero, it is not possible to take a step to the left, and so there are only two available controls.
%

\begin{code}
data ZAction : Set where
  ZS  : ZAction -- stay
  ZR  : ZAction -- right
\end{code}

%
We can encode this behaviour since the control is depending on the state.
%
If the state is zero, the available controls are those defined in the |ZAction| data type.
%
Otherwise the available controls are those defined in the |SAction| data type.
%

\begin{code}
oned-control  :  oned-state -> Set
oned-control zero     = ZAction
oned-control (suc n)  = SAction
\end{code}

%
The step functions is swiftly implemented, pattern matching on the states and controls.
%
\begin{code}
oned-step  :  (x : oned-state) -> oned-control x -> oned-state
oned-step  zero ZS      = zero
oned-step  zero ZR      = suc zero
oned-step  (suc n)  SL  = n
oned-step  (suc n)  SS  = suc n
oned-step  (suc n)  SR  = suc (suc n)
\end{code}
%
Finally, a sequential decision process can be defined.
%
\begin{code}
system  :  SDProc
system  =  SDP oned-state oned-control oned-step
\end{code}
%
If we wish to run this system and see an example of a trajectory, we need to define some policies.
%
Based on what state the system is in a policy will return a control.
%
The first policy we define we will name |tryleft|.
%
We name it so since there is no way to move left if the state is zero.
%
If this is the case, the policy will return a control that does nothing.
%
\begin{code}
tryleft : Policy system
tryleft zero     = ZS
tryleft (suc s)  = SL
\end{code}
%
The policies for stay and right are easy, as there are no corner cases.
%
\begin{code}
stay : Policy system
stay zero     = ZS
stay (suc s)  = SS

right : Policy system
right zero     = ZR
right (suc s)  = SR
\end{code}
%
A policy sequence is now just a vector of policies.
%
\begin{code}
sequence : Vec (Policy system) 5
sequence = tryleft ∷ tryleft ∷ right ∷ stay ∷ right ∷ []
\end{code}
%
We can now evaluate the system using this sequence, starting from different points.
%
We can use |≡| and |refl| to assert that the system behaves as intended.
%
\begin{code}
test1 : trajectory system sequence 0 ≡ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ []
test1 = refl

test2 : trajectory system sequence 5 ≡ 4 ∷ 3 ∷ 4 ∷ 4 ∷ 5 ∷ 5 ∷ []
test2 = refl
\end{code}

%
Now, how to turn a process into a problem?
%
We need to introduce some sort of goal, described by a |reward| function.
%
For our example we define the reward function to be parameterised over a target coordinate.
%
The reward function could then reward a proposed step based on how close to the target it lands.
%

%if false
\begin{code}
distance : ℕ → ℕ → ℕ    -- distance m n = abs (m-n)  informally
distance zero zero       = 0
distance zero (suc m)    = 1 + distance zero m
distance (suc n) zero    = 1 + distance n zero
distance (suc n) (suc m) = distance n m
\end{code}
%endif

\begin{code}
large-number : ℕ
large-number = 10000

oned-reward :  oned-state
           ->  (x : oned-state) -> oned-control x -> oned-state
           ->  ℕ
oned-reward target x0 y x1
  = large-number  ∸ (distance target x1)
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

\TODO{Example ``run'' would be instructive}
