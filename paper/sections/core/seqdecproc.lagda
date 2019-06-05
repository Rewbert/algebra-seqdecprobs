% -*- latex -*-

%if false
\begin{code}

module core.seqdecproc where
open import Data.Nat
open import Data.Vec

\end{code}
%endif

\subsection{Sequential Decision Process}
\label{subsec:seqdecproc}
%
We can extend the idea of a |dynamic system| to that of a |sequential decision process| by introducting a notion of control.
%
A control captures the idea of an action that is possible at a given state.
%
Since the available actions depend on what state the process is in, the control is a predicate on the state.
%
To exemplify this we consider the case of an airplane that can only execute the action of lifting the landing gears if the plane is airborne.
%
\begin{code}
Policy : (S : Set) → ((s : S) → Set) → Set
Policy S C = (s : S) → C s

record SDProc : Set1 where
  constructor SDP
  field
    State    : Set
    Control  : State -> Set
    step     : (x : State) -> Control x -> State
  Pol = Policy State Control
  St  = State

-- Can these be defined here?  #st, #pol, #c
-- open SDProc
-- postulate hej : (P : SDProc) -> Vec (SDProc.Pol P) 3
-- postulate haj : (P : SDProc) -> State P
\end{code}

%if false
\begin{code}
#st_ : SDProc → Set
#st_ = SDProc.St --SDP State Control step = State

infix 30 #st_

#c_ : (s : SDProc) → (#st s → Set)
#c SDP State Control step = Control

#sf_ : (s : SDProc) → ((x : #st s) → (y : (#c s) x) → #st s)
#sf SDP State Control step = step
\end{code}
%endif

%
Many different controls could be available at each step.
%
To decide which control should be selected at a state we resort to the notion of a Policy.
%
\begin{code}
-- Policy : (S : Set) → ((s : S) → Set) → Set
-- Policy S C = (s : S) → C s
\end{code}
%
If we want to make |n| transitions we need a sequence of |n| policies.
%
We define a sequence of policies in terms of a vector.
%
\begin{code}
PolicySeq : (S : Set) → ((s : S) → Set) -> ℕ -> Set
PolicySeq S C n = Vec (Policy S C) n
\end{code}
%
Now we have all the definitions we need in order to implement the trajectory function for sequential decision processes.
%
\begin{code}
trajectory  :   {n : ℕ}
            ->  (p : SDProc) -> PolicySeq (#st p) (#c p) n -> #st p
            ->  Vec (#st p) n
trajectory sys []        x0  = []
trajectory sys (p ∷ ps)  x0  = x1 ∷ trajectory sys ps x1
  where  x1  :  #st sys
         x1  =  (#sf sys) x0 (p x0)
\end{code}
%
