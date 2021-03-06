% -*- latex -*-
\section{Combinators for sequential decision processes}
\label{sec:combsecdecproc}

%if false
\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module combinators where

open import core.seqdecproc
open import examples

open import Data.Nat hiding (_^_)
open import Agda.Builtin.Nat
open import Data.Bool
open import Data.Product hiding (swap)
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Fin hiding (lift)
open import Data.Maybe
open import Data.Vec

Con : Set → Set₁
Con S = S → Set

Step : (S : Set) -> Con S -> Set
Step S C = (s : S) -> C s -> S

\end{code}
%endif

%
Now that we've seen an example of a sequential decision process and are getting comfortable with the concept, it is suitable to move forward and see what we can do with processes.
%
This section will explore different ways sequential decision processes can be combined in order to produce more sophisticated processes.
%
%-----------------------------------------------------------------------

%
We already defined the product combinator, and before we move on to additional combinators we'd like to make a few notes on the product combinator.
%
An observation to be made is that in order for the new system to exist in any state, it has to hold components of both prior states.
%
This has the consequence that if the state space of one of the prior processes is empty, the new problems state space is also empty.
%
Similarly, if one of the components reaches a point where there are no available controls, and thus can not progress, the other component will not be able to progress either.
%

%include 2dexamples.lagda

%
Functional programmers will often find they are in need of a unit, e.g when using |reduce| or other frequently appearing constructs from the functional paradigm.
%
Before we begin implementing a unit for the product case we want to clarify what we mean by a unit.
%
A unit to a process is one that when combined with another process, produces a process where the change at each step is exactly that of the other process.
%

%
What we are after is a process that will not carry any extra information, or rather one that can not alter the information it carries.
%
Recall that in order for the state space of the product process to not be empty, both state spaces of the separate processes has to be non-empty.
%
In order to call the step function the control space also has to be inhabited.
%
In an effort to minimise the information the unit carries we declare its state space and control space to be singletons.
%
The step function becomes a constant function that given the only state and the only control, will return the only state.
%
\begin{code}
singleton : SDProc
singleton = record {
  State    =  ⊤;
  Control  =  λ state -> ⊤;
  step     =  λ state -> λ control -> tt}
\end{code}
%
An example of evaluating the singleton process is illustrated in Figure \ref{images:singleton}
%
\begin{figure}
\centering
\includegraphics[scale=0.7]{images/singleton.png}
\caption{Illustration of the singleton process. The subscript ₀ is meant to indicate that the state remains the same when the process advances.}
\label{images:singleton}
\end{figure}

%
Taking the product of any process and the singleton process would produce a process where the only change of information during each step is that of the process which is not the singleton.
%
Of course, the other process could itself be the singleton process also, in which case the only change in each step is exactly that of the singleton process, which is no change at all.
%

%-----------------------------------------------------------------------
\subsection{Coproduct}
\label{subsec:coproductseqdecproc}

%
Seeing how we defined a product combinator of two processes, we are interested in also defining a sum combinator for processes.
%
The approach is similar to that of the product case.
%

%
The inhabitants of the sum control is the sum of the inhabitants of the prior controls.
%
\begin{code}
_⊎C_  :  {S₁ S₂ : Set}
      →  Con S₁ → Con S₂ → Con (S₁ ⊎ S₂)
(C₁ ⊎C C₂) (inj₁ s₁)  = C₁ s₁
(C₁ ⊎C C₂) (inj₂ s₂)  = C₂ s₂
\end{code}
%
Calculating a new step function from two prior step functions is relatively straight forward.
%
The first input is the sum of the two states.
%
Depending on which state the first argument belongs to, one of the prior step functions is applied to it and the second argument, the control for that state.
%
The result of the application is then injected into the sum type using the same injection as the input.
%
\begin{code}
_⊎sf_  :   {S₁ S₂ : Set}
       ->  {C₁ : Con S₁} -> {C₂ : Con S₂}
       ->  Step S₁ C₁ -> Step S₂ C₂
       ->  Step (S₁ ⊎ S₂) (C₁ ⊎C C₂)
(sf₁ ⊎sf sf₂) (inj₁ s₁) c₁  = inj₁ (sf₁ s₁ c₁)
(sf₁ ⊎sf sf₂) (inj₂ s₂) c₂  = inj₂ (sf₂ s₂ c₂)
\end{code}
%
The sum of two problems is computed by applying the sum operators componentwise, and Figure \ref{images:coproduct} illustrate how such a problem is evaluated.
%
\begin{code}
_⊎SDP_ : SDProc → SDProc → SDProc
SDP S₁ C₁ sf₁ ⊎SDP SDP S₂ C₂ sf₂
  = SDP (S₁ ⊎ S₂) (C₁ ⊎C C₂) (sf₁ ⊎sf sf₂)
\end{code}

\begin{figure}
\begin{subfigure}{.5\textwidth}
  \centering
  % include first image
  \includegraphics[width=.8\linewidth]{images/coproduct-inj1.png}
  \caption{Left injection.} % write better captions
  \label{images:coproduct-inj1}
\end{subfigure}
\begin{subfigure}{.5\textwidth}
  \centering
  % include second image
  \includegraphics[width=.8\linewidth]{images/coproduct-inj2.png}
  \caption{Right injection.}
  \label{images:coproduct-inj2}
\end{subfigure}
\caption{The coproduct of two processes. The process will take the shape of either of the two alternatives, but never both or a mix of the two.}
\label{images:coproduct}
\end{figure}

%
In the case of the product process the two prior processes were not entirely independent.
%
If one process could not progress the other process was \emph{affected} in the sense that it too could not progress further.
%
The sum of two processes keeps the two problems truly independent.
%
In fact, the coproduct of two processes will start progressing from some initial state, and depending on which injection is used the other process will never advance.

%
A unit to the coproduct combinator is the empty process.
%
The process has no states, no controls and the step function will return its input state.
%
However, we will never be able to call the step function since we can not supply a state.
%
\begin{code}
empty : SDProc
empty = record {
  State    = ⊥;
  Control  = λ state -> ⊥;
  step     = λ state -> λ control -> state }
\end{code}

%
Combining any process with the empty process using the coproduct combinator will produce a process that acts exactly as that of the given process.
%
There is no way to begin advancing the empty process, and so the only available option is to select an initial state from the other process and start progressing that.
%

%-----------------------------------------------------------------------
\subsection{Yielding Coproduct}
\label{subsec:yieldingcoproductseqdecproc}

%
Computing the coproduct of two processes and getting a process that behaves like either of the two, without actually considering the other process, leaves us wondering what this is useful for.
%
It would be more useful if we could jump between the two processes.
%
To do this, we first need to define a relation between states.
%
We define a relation on two state and define it to be a mapping from an inhabitant of one state to an inhabitant of the other.
%
\begin{code}
_⇄_ : (S₁ S₂ : Set) → Set
s₁ ⇄ s₂ = (s₁ -> s₂) × (s₂ -> s₁)
\end{code}
%
Combining the two controls on the states is similar to that of the coproduct case, when looking at the type.
%
However, instead of the new control being defined as either of the two prior ones, it is now |Maybe| either of the two previous ones.
%
The idea is that we extend the control space to have one more inhabitant, the value |nothing|.
%
If we select this control the process should yield in favour of the other process.
%
\begin{code}
_⊎C+_  :  {S₁ S₂ : Set}
       →  Con S₁ → Con S₂ → Con (S₁ ⊎ S₂)
(C₁ ⊎C+ C₂) (inj₁ s₁) = Maybe (C₁ s₁)
(C₁ ⊎C+ C₂) (inj₂ s₂) = Maybe (C₂ s₂)
\end{code}
%
The new step function needs to accomodate for this scenario where the process should yield in favour of the other.
%
To implement this the new step function needs to know \emph{how} to yield.
%
We describe how to yield by supplying an element of type |S₁ ⇄ S₂|.
%
If the selected control is |nothing| the step function will apply the appropriate component of this element to the current state.
%
\begin{code}
⊎sf+  :  {S₁ S₂ : Set} {C₁ : Con S₁} {C₂ : Con S₂}
      →  (S₁ ⇄ S₂)
      →  Step S₁ C₁ → Step S₂ C₂
      →  Step (S₁ ⊎ S₂) (C₁ ⊎C+ C₂)
⊎sf+ _          sf₁ sf₂  (inj₁ s₁)  (just c)  = inj₁ (sf₁ s₁ c)
⊎sf+ _          sf₁ sf₂  (inj₂ s₂)  (just c)  = inj₂ (sf₂ s₂ c)
⊎sf+ (v₁ , _ )  sf₁ sf₂  (inj₁ s₁)  nothing   = inj₂ (v₁ s₁)
⊎sf+ (_  , v₂)  sf₁ sf₂  (inj₂ s₂)  nothing   = inj₁ (v₂ s₂)
\end{code}
Since the other operators were infix, we give a syntax declaration that mimics the same style.
\begin{code}
syntax ⊎sf+ r sf₁ sf₂  =  sf₁ ⟨ r ⟩ sf₂
\end{code}
%
Now we can compute the yielding coproduct of two processes by applying the new operations componentwise.
%
\begin{code}
_⊎SDP+_  :  (p₁ : SDProc) → (p₂ : SDProc)
         →  (#st p₁  ⇄  #st p₂)
         →  SDProc
((SDP S₁ C₁ sf₁) ⊎SDP+ (SDP S₂ C₂ sf₂)) rel
  = SDP (S₁ ⊎ S₂) (C₁ ⊎C+ C₂) (sf₁ ⟨ rel ⟩ sf₂)
\end{code}
\begin{figure}
\label{images:yieldcoproduct}
\centering
\includegraphics[scale=0.7]{images/yieldcoproduct.png}
\caption{Illustration of the yielding coproduct process. It is capable of switching between the two processes, as illustrated by the calls to v1 and v2.}
\end{figure}

%
With a combinator such as this one could you model e.g a two player game.
%
The processes would be the players and the combined process allows each to take turns making their next move.
%
In section \ref{sec:policycombinators} we discuss how a policy for such a process is something of a game leader.
%

%
A unit to the yielding coproduct combinator is the same one as that for the regular coproduct combinator.
%
If the state space is not inhabited, the process could never progress as we will not be able to call the step function.
%
Further more, we would not be able to give a definition for a function |S₁ -> S₂|.
%

%-----------------------------------------------------------------------
\subsection{Interleaving processes}
\label{subsec:interleavingseqdecproc}
%
The next combinator we introduce is one that interleaves processes.
%
The state of such a process holds components of both prior states, but takes turns applying the step function to each of them.
%
This behaviour could be similar to that of a game, where two players take turns making their next move.
%
However, the users do not know what moves the other player has made, and can therefore not make particularly smart moves.
%
In section \ref{sec:policycombinators} it is reasoned that writing new policies for a process like this will be a policy that does know what move the other 'player' has made.
%

%
Similar to the product combinator the new state needs to hold components of both prior states.
%
It should apply the step function to them one at a time, alternating between the two.
%
In order to know which components turn it is to advance we extend the product to also hold an index.
%
\begin{code}
_⇄S_ : Set → Set → Set
S₁ ⇄S S₂ = Fin 2 × S₁ × S₂
\end{code}
%
The control space for the interleaved process is the sum of the two prior control spaces.
%
If the value of the first component is zero, we select the first control.
%
If the value is one, we select the second control.
%
\begin{code}
one : Fin 2
one = suc zero

_⇄C_  :  {S₁ S₂ : Set}
      →  Con S₁ → Con S₂ → Con (S₁ ⇄S S₂)
(C₁ ⇄C C₂) (zero , s₁ , s₂)  = C₁ s₁
(C₁ ⇄C C₂) (one , s₁ , s₂)   = C₂ s₂
\end{code}
%
Defining a new step function in terms of the two previous ones is done by pattern matching on the state.
%
Specifically we are interested in the first component, the index.
%
If the index is zero we apply the first step function to the second component of the state, leave the last component unchanged and increment the index by one.
%
Similarly if the index is zero we apply the second step function to the last component, leave the second one unchanged and decrement the index by one.
%
\begin{code}
_⇄sf_  :  {S₁ S₂ : Set}
       →  {C₁ : Con S₁} → {C₂ : Con S₂}
       →  Step S₁ C₁ → Step S₂ C₂
       →  Step (S₁ ⇄S S₂) (C₁ ⇄C C₂)
(sf₁ ⇄sf sf₂) (zero , s₁ , s₂) c  = (one , sf₁ s₁ c , s₂)
(sf₁ ⇄sf sf₂) (suc zero , s₁ , s₂) c   = (zero , s₁ , sf₂ s₂ c)
(sf₁ ⇄sf sf₂) (suc (suc ()) , _ , _)
\end{code}
%
Combining two processes to capture this interleaved behaviour is once again simply done by combining the components componentwise.
%
\begin{code}
_⇄SDP_ : SDProc → SDProc → SDProc
SDP S₁ C₁ sf₁ ⇄SDP SDP S₂ C₂ sf₂
  = SDP (S₁ ⇄S S₂) (C₁ ⇄C C₂) (sf₁ ⇄sf sf₂)
\end{code}
%
The final process behaves as illustrated in figure \ref{images:interleave}.
%

\begin{figure}
\centering
\includegraphics[scale=0.7]{images/interleave.png}
\caption{Illustration of two interleaved process. We want to emphasise that the state holds components of both prior states, but chooses to advance only one. The policy that chooses what control to use can however inspect both components.}
\label{images:interleave}
\end{figure}

%
Defining a unit for the interleaved process is not possible.
%
Where the initial process would advance e.g five steps, the interleaved process would need ten steps to take that component to the same state.
%
We can not give a generic process that when interleaved with another process acts as a unit.

The way we define the interleaved combinator might not be optimal.
%
Combining more than two processes will produce potentially unexpected behaviour.
%
If we combine three processes using this combinator the resulting system would be one where one of the processes advance half the time, and the other two only a quarter of the time each.
%
\begin{figure*}[htbp]
  \begin{subfigure}[b]{.8\textwidth}
    \centering
    \includegraphics[scale=0.8]{images/badinterleave2.png}
    \caption{If we interleave two processes and then interleave the resulting process with a third we get a situation like this. They are not properly interleaved.}
    \label{images:badinterleave}
  \end{subfigure}
  \begin{subfigure}[b]{.8\textwidth}
    \centering
    \includegraphics[scale=0.8]{images/wantedinterleave2.png}
    \caption{This is the interleaved behaviour we might expect for three processes. A round robin behaviour that gives the processes equally many turns.}
    \label{images:wantedinterleave}
  \end{subfigure}
  \caption{Illustrations of why the interleaved combinator might not behave as one would expect. Again the two incoming arrows illustrate that the policy that selects the control has access to all components and can base the choice of control on them.}
  \label{images:badvsgoodinterleave}
\end{figure*}

%
This does not necessarily mean that the combinator described in Figure \ref{images:badvsgoodinterleave}  is wrong, but rather that there is another combinator we could implement that would have this other behaviour.
%
