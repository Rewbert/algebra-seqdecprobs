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

open import core.seqdecproc hiding (Policy; PolicySeq; #st_; trajectory)
open import Data.Nat
open import Data.Fin
open import Data.Vec
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
#st = SDProcT.State
#sf = SDProcT.step
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

\subsection{A discussion on the |Fin| type}
\label{subsec:fintype}
%
Before we move on to an example of a time dependent process, we need to briefly present the |Fin| type and its properties.
%
The |Fin n| type (for any natural number |n|) has exactly |n| elements.
%
> data Fin : ℕ → Set where
>   zero  : {n : ℕ}              → Fin (suc n)
>   suc   : {n : ℕ} (i : Fin n)  → Fin (suc n)
%
From this definition we see that |zero| is an element of |Fin n| for any |n > zero|.
%
The constructor |suc| takes an element of type |Fin n| and returns an element of type |Fin (suc n)|.
%
Let's illustrate the type for a couple of different n's.
%
\begin{figure}
\centering
\includegraphics[scale=0.7]{images/finn.png}
\caption{Illustration of the Fin type.}
\label{images:finn}
\end{figure}

%
Illustrating what |suc| does comes as no surprise.
%
It takes an element of |Fin n| and give us the sucessor in |Fin (suc n)|.
%TODO: cut the "middle two" n, n+1 to fit in the width. May need to use figure* for a 2col-wide figure in ACM style.
\begin{figure}
\centering
\includegraphics[scale=0.8]{images/suc.png}\includegraphics[scale=0.8]{images/inject.png}\includegraphics[scale=0.8]{images/injectinject.png}
\caption{|suc| takes an element of type |Fin n| and gives us the sucessor element of type |Fin (suc n)|.}
\label{images:suc}
\end{figure}

%
What if we want to change the type of an element?
%
In figure \ref{images:embed} it becomes clear that all elements of type |Fin n| are also elements of |Fin (suc n)|.
%
We sould be able to embed any element from |Fin n| into |Fin (suc n)|.
\begin{figure}
\centering
\includegraphics[scale=0.8]{images/embed.png}
\caption{The sucessor type of |Fin n| only has one more element. We should have an embedding like this.}
\label{images:embed}
\end{figure}
%
To do this we use the function inject₁.
%
> inject₁ : ∀ {m} → Fin m → Fin (suc m)
> inject₁ zero     = zero
> inject₁ (suc i)  = suc (inject₁ i)
%
It should be clear here that the element is left intact while the type changes.
%
\begin{figure}
\centering
\includegraphics[scale=0.8]{images/inject.png}
\caption{Inject takes any element of type |Fin n| and returns the same element of type |Fin (suc n)|.}
\label{images:inject}
\end{figure}

% \TODO{clear this up a bit}
Now, what if we find ourselves in a situation where we have a number in |Fin (suc n)|, and we want to return its predecessor, but of type |Fin (suc (suc n))|?
%
What we want to do is given an element |suc x|, return x.
%
We can't do this as is since the element |suc x| is of type |Fin (suc n)|, the element x is of type |Fin n|.
%
To solve this problem we need to invoke |inject₁| twice.
% \TODO{image does not align properly}
\begin{figure}
\centering
\includegraphics[scale=0.8]{images/injectinject.png}
\caption{One way to implement the predecessor function for |Fin (suc n)|, while returning an element of the sucessor type.}
\label{images:injectinject}
\end{figure}

\subsection{Time dependent example} % need better section title
\label{subsec:timedependentexample}
%
Looking back at the time independent example, we reflect on the choice of state.
%
The natural numbers seemed, and were, a reasonable choice.
%
With the time dependent process at our disposal however we notice a source of ineffectiveness.

% \TODO{Only if initial state is zero?}
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
However, if the state is greater than |zero| we need to change the types as described in section \ref{subsec:fintype}.
%
For the left control the result has to be injected twice, and for the stay control it has to be injected once.
%
\begin{code}
oned-step  :   (n : ℕ)
           →  (x : oned-state n) → (y : oned-control n x) → oned-state (suc n)
oned-step n zero     ZS  = zero
oned-step n zero     ZR  = suc zero
oned-step n (suc x)  SL  = inject₁ (inject₁ x)
oned-step n (suc x)  SS  = inject₁ (suc x)
oned-step n (suc x)  SR  = suc (suc x)
\end{code}
%
Now the entire system has been defined and we can package it as a |SDProcT|.
%
\begin{code}
finsystem : SDProcT
finsystem = SDPT oned-state oned-control oned-step
\end{code}
