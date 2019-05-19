% -*- latex -*-
\section{Time dependent processes}
\label{sec:timedependentcase}

%
Imagine a process where the state space can vary over time.
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
    step     : (t : ℕ)
           →  (x : State t) → Control t x → State (suc t)
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
A time independent process can be embedded as a time dependent process.
%
The embedding is a process that disregards the time parameter.
%
\begin{code}
embed : SDProc → SDProcT
embed (SDP S C sf)
  = SDPT (λ _ → S) (λ _ → C) (λ _ → sf)
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
We illustrate the type for a couple of different n's in figure \ref{images:finn}.
%
\begin{figure}
\centering
\includegraphics[scale=0.7]{images/finn.png}
\caption{An illustration of the |Fin n| type. We emphasise that there are exactly |n| inhabitants of |Fin n|.}
\label{images:finn}
\end{figure}

\begin{figure*}[htbp]
  \begin{subfigure}[b]{.20\textwidth}
    \hbox{\hspace{-0.5em} \includegraphics[scale=0.75]{images/suc.png}} % \TODO{add suc annot to image or remove inject annot from the others}
    \caption{}
    \label{images:suc}
  \end{subfigure}
  \begin{subfigure}[b]{.20\textwidth}
    \centering
    \includegraphics[scale=0.75]{images/inject.png}
    \caption{}
    \label{images:inject}
  \end{subfigure}
  \begin{subfigure}[b]{.20\textwidth}
    \centering
    \includegraphics[scale=0.75]{images/injectinject.png}
    \caption{}
    \label{images:injectinject}
  \end{subfigure}
  \begin{subfigure}[b]{.20\textwidth}
    \centering
    \includegraphics[scale=0.75]{images/embed.png}
    \caption{}
    \label{images:embed}
  \end{subfigure}

  \caption{Illustrations of how to embed elements of type |Fin n| in the sucessor type |Fin (suc n)|.}
  \label{images:fin}
\end{figure*}

%
We illustrate what the |suc| constructor does in figure \ref{images:suc}.
%
It takes an element of type |Fin n|, and returns the sucessor element of type |Fin (suc n)|.
%

%
What if we want an element of the sucessor type without using the suc constructor?
%
We might wish to simply 'promote' the type of an element.
%
In figure \ref{images:embed} it becomes clear that all elements of type |Fin n| are also elements of |Fin (suc n)|.
%
To do this promoting we use the function inject₁, which is illustrated in figure \ref{images:inject}.
%
> inject₁ : ∀ {m} → Fin m → Fin (suc m)
> inject₁ zero     = zero
> inject₁ (suc i)  = suc (inject₁ i)
%

Now, what if we find ourselves in a situation where we have an element of type |Fin (suc n)|, and we want to return its predecessor, but of the sucessor type \emph{Fin (suc (suc n))}?
%
What we want to do is given an element |suc x|, return |x|.
%
We can't do this as is since the element |suc x| is of type |Fin (suc n)|, the element |x| is of type |Fin n|.
%
To get the proper type we need to invoke |inject₁| twice, which is illustrated in figure \ref{images:injectinject}.

\subsection{Time dependent example}
\label{subsec:timedependentexample}
%
Looking back at the time independent example, we reflect on the choice of state.
%
The natural numbers seemed, and were, a reasonable choice.
%
With the time dependent process at our disposal however we notice a source of ineffectiveness.
%

\TODO{Everything looks too crowded when this image is below the other big image.}
%if False
\begin{figure*}
  \begin{subfigure}[b]{.30\textwidth}
    \centering
    \includegraphics[scale=0.75]{images/generalcasefin}
    \caption{How the state space grows in the general case, where we can either increment, decrement or do nothing.}
    \label{subfig:generalcasefin}
  \end{subfigure}
  \begin{subfigure}[b]{.30\textwidth}
    \centering
    \includegraphics[scale=0.75]{images/edgecasefin}
    \caption{In the edge case the state space grows slower, as we initially can not decrement the state.}
    \label{subfig:edgecasefin}
  \end{subfigure}
\caption{Illustration of the state space of a time dependent process grows where the state are the natural numbers.}
\label{fig:finex}
\end{figure*}
%endif

%
In the general case we could only be in three different states after one step.
%
Either we stayed, went left or we went right.
%
After two steps we could be in any of five possible states.
%
This behaviour is illustrated in figure \ref{fig:generalcasefin}.
%
\begin{figure}[H]
  \centering
  \includegraphics[scale=0.75]{images/generalcasefin}
  \caption{How the state space grows in the general case, where we can either increment, decrement or do nothing.}
  \label{fig:generalcasefin}
\end{figure}
%
This can be generalised to saying that at time |n| the number of possible states are |n + 2|.
%
In figure \ref{fig:edgecasefin} the edge case is illustrated, and we note that the number of possible states after n steps are |n+1|.
%
\begin{figure}[H]
  \centering
  \includegraphics[scale=0.75]{images/edgecasefin}
  \caption{In the edge case the state space grows slower, as we initially can not decrement the state.}
  \label{fig:edgecasefin}
\end{figure}
%
If we consider the example from earlier but restrict it to starting in state zero, we could define this process as follows.
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
oned-step  :  (n : ℕ) → (x : oned-state n)
           →  (y : oned-control n x) →  oned-state (suc n)
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
