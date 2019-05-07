% -*- latex -*-
\section{Time dependent case}
\label{sec:timedependentcase}

%
Imagine a process where the state can vary over time.
%
If we consider the example with the one dimensional coordinate system, if the process is time dependent it could disallow some states at certain points in time.
%
Below we illustrate how this is defined in Agda.
%
%if false
\begin{code}
module core.seqdecproctime where

open import core.seqdecproc
open import Data.Nat
\end{code}
%endif
\begin{code}
record SDProcT : Set₁ where
  constructor SDPT
  field
    State    : (t : ℕ) → Set
    Control  : (t : ℕ) → State t → Set
    step     : (t : ℕ) → (x : State t) → Control t x → State (suc t)
\end{code}
%if false
\begin{code}
#stᵗ = SDProcT.State
#sfᵗ = SDProcT.step
\end{code}
%endif
%
What are we actually saying here?
%
The state is now dependent on a parameter |t : ℕ|, which allows the state to take on alternate forms.
%

%
An attempt to illustrate what this means is done below.
%
The process we want to define model the day of a computer scientist.
%
During the day all the researcher can do is either read papers or eat food.
%
\begin{code}
data Day : Set where
  Eating   : Day
  Reading  : Day
\end{code}
%
During the night they can either sleep, write code or grade papers.
%
\begin{code}
data Night : Set where
  Sleeping  : Night
  Coding    : Night
  Grading   : Night
\end{code}
If we take 1 time step to mean 6 hours, we can model what they can do by having the state |very| depending on the time.
\begin{code}
1d-state' : ℕ → Set
1d-state' zero                       = Day         -- first 6 hours of day
1d-state' (suc zero)                 = Day         -- last 6 hours of day
1d-state' (suc (suc zero))           = Night       -- first 6 hours of night
1d-state' (suc (suc (suc zero)))     = Night       -- last 6 hours of night
1d-state' (suc (suc (suc (suc n))))  = 1d-state' n
\end{code}
%
This way of defining the state gives more flexibility in what you can model.
%
Now not only can the control space change as the state changes, but the state space can change as the time changes.
%


%
There is a trivial embedding of a sequential decision process as a time dependen process.
%
The embedding produces a process that does not use the fact that the state is time dependent.
%
\begin{code}
embed : SDProc → SDProcT
embed (SDP S C sf) = SDPT (λ _ → S) (λ _ → C) (λ _ → sf)
\end{code}
