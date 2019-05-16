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
Because not all actions are possible in all states the control is depending on what state the process is currently in.
%
\begin{code}
record SDProc : Set1 where
  constructor SDP
  field
    State    : Set
    Control  : State -> Set
    step     : (x : State) -> Control x -> State
\end{code}

%if false
\begin{code}
#st_ : SDProc → Set
#st SDP State Control step = State

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
Which control is actually used to transition from one state to the next  is specified by a |Policy|.
%
\begin{code}
Policy : SDProc -> Set
Policy (SDP S C _) = (x : S) -> C x
\end{code}
%
To compute |n| transitions we need a sequence of |n| policies.
%
\begin{code}
PolicySeq : SDProc -> ℕ -> Set
PolicySeq system n = Vec (Policy system) n
\end{code}
%
Now we have all the definitions we need in order to implement the trajectory function for sequential decision processes.
%
\begin{code}
trajectory  :   {n : ℕ}
            ->  (p : SDProc) -> PolicySeq p n -> #st p
            ->  Vec (#st p) (suc n)
trajectory sys []        x0  = x0  ∷ []
trajectory sys (p ∷ ps)  x0  = x1 ∷ trajectory sys ps x1
  where  x1  :  #st sys
         x1  =  (#sf sys) x0 (p x0)
\end{code}
%
