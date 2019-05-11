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
open import Data.Fin
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
The state is now dependent on a parameter |t : ℕ|, which allows the state to take on alternate forms.
%
In section \ref{subsec:timedependentexample} we illustrate what this means.
%

%
We note here that there is a trivial embedding of a sequential decision process as a time dependen process.
%
The embedding produces a process that does not use the fact that the state is time dependent.
%
\begin{code}
embed : SDProc → SDProcT
embed (SDP S C sf) = SDPT (λ _ → S) (λ _ → C) (λ _ → sf)
\end{code}

\subsection{Time dependent example} % need better section title
\label{subsec:timedependentexample}
%
Looking back at the time independent example, we reflect on the choice of state.
%
The natural numbers seemed, and were, a reasonable choice.
%
With the time dependent process at our disposal however we notice a source of ineffectiveness.

%
The state space is all the natural numbers even when we haven't taken a step yet.
%
After 1 step the possible states we could inhabit are only two.
%
Either we stayed or we turned left or right.
%
Similarly after 2 steps we could only be in any of three possible states.
%

%
We can encode this behaviour in the state space of the coordinate system as follows.
%
\begin{code}
oned-state : ℕ → Set
oned-state n = Fin (suc n)
\end{code}
%
The Agda type |Fin n| is a type with at most |n| elements.
%
Using this type gives us a more precise definition of what the possible states are.
%

%
The controls are identical to those in the time independent case.
%if false
\begin{code}
data ZAction : Set where
  ZS :  ZAction
  ZR :  ZAction

data SAction : Set where
  SL :  SAction
  SS :  SAction
  SR :  SAction
\end{code}
%endif
\begin{code}
oned-control : (n : ℕ) → oned-state n → Set
oned-control n zero     = ZAction
oned-control n (suc x)  = SAction
\end{code}

%
The step function says the same thing as in the previous example, but it says it a little differently.
%
If the state is zero there is only two available controls, and we update the state like we did previously.
%
\begin{code}
oned-step : (n : ℕ) → (x : oned-state n) → (y : oned-control n x) → oned-state (suc n)
oned-step n zero     ZS  = zero
oned-step n zero     ZR  = suc zero
\end{code}
%
In the successor case we need to play a bit with the types to get our meaning across.
%
If we supplied the left control we previously changed our state from |suc n| to |n|.
%
Now we have a state |suc n| of type |Fin n|, and we wish to return |n| and have it be of type |Fin (suc n)|.
%
However |n| is of type |Fin (pred n)|, and so we need to inject it into the sucessor type by applying |inject₁| to it.
%
We do this twice to achieve an element of the proper type.
%
\begin{code}
oned-step n (suc x)  SL  = inject₁ (inject₁ x)
\end{code}
%
Simialarly for the stay control we wish to leave the state unchanged but change the type of it.
%
We inject the state unchanged and turn it from being an inhabitant of |Fin n| to one of |Fin (suc n)|.
%
\begin{code}
oned-step n (suc x)  SS  = inject₁ (suc x)
\end{code}
%
The case where we actually increment the state is straight forward.
%
The |Fin n| will become a |Fin (suc n)| by using the |suc| constructor.
%
\begin{code}
oned-step n (suc x)  SR  = suc (suc x)
\end{code}

%
Now the entire system has been defined and we can package it as a |SDProcT|.
%
\begin{code}
finsystem : SDProcT
finsystem = SDPT oned-state oned-control oned-step
\end{code}
