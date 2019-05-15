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
open import Data.Bool
open import Data.Product hiding (swap)
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Fin hiding (lift)
open import Data.Maybe
open import Data.Vec

\end{code}
%endif

%
Now that we've seen a few examples and are getting comfortable with the notion of sequential decision problems, it is suitable to more forward and see what we can do with such problems.
%
This section will explore different ways sequential decision processes can be combined in order to produce more sophisticated processes.
%
%-----------------------------------------------------------------------
\subsection{Product}
\label{subsec:productseqdecproc}
%
A first example of how two problems can be combined is to create their product.
%
Naturally the new state is just the product of the two prior states.
%
The other components, the |Control| and the |step| must be described and combined more thoroughly.
%
The control is a predicate on the state, and if we consider the control as such we can consider the state to be a term.
%
\TODO{Use consistent constructor/variable names/cases also elsewhere}
%
\begin{code}
Pred : Set → Set₁
Pred S = S → Set
\end{code}
%
Given two terms and two predicates, one on each term, we compute the predicate on the product of the two terms.
%
The inhabitants of this product predicate are pairs of the inhabitants of the prior predicates.
%
\begin{code}
_×C_ :   {S₁ S₂ : Set}
     ->  Pred S₁ -> Pred S₂ -> Pred (S₁ × S₂)
(C₁ ×C C₂) (s₁ , s₂) = C₁ s₁ × C₂ s₂
\end{code}
%
% insert connor mcbride discussion here i suppose.
%
After defining what State and Controls are, terms and predicates, we want to relate to the step function in a similar manner.
%
From predicate logic we recall that functions are also terms. % they are terms if they are applied to n terms (the predicate is not a term?)
%
Given a term and a predicate on that term, the step function produces a new term of the same type.
%
\begin{code}
Step : (S : Set) -> Pred S -> Set
Step S C = (s : S) -> C s -> S
\end{code}
%
Next we want to compute the product of two such step functions.
%
The function is given two terms |S₁| and |S₂|.
%
Two predicates |C₁ : Pred S₁| and |C₂ : Pred S₂|, and lastly two functions |Step S₁ C₁| and |Step S₂ C₂|.
%
From this input we must define a function that given an element of the product of the terms |S₁ × S₂| and the product of the predicates |C₁ ×C C₂"| produces a new term.
%
The result is a product of terms that are computed by componentwise calling the prior step functions.
%
\begin{code}
_×sf_  :   {S₁ S₂ : Set}
       ->  {C₁ : Pred S₁} -> {C₂ : Pred S₂}
       ->  Step S₁ C₁ -> Step S₂ C₂
       ->  Step (S₁ × S₂) (C₁ ×C C₂)
(sf₁ ×sf sf₂) (s₁ , s₂) (c₁ , c₂) = (sf₁ s₁ c₁ , sf₂ s₂ c₂)
\end{code}

%
Seeing how we know how to combine all components on the bases of a product, computing the product of two sequential decision processes becomes easy.
%
We componentwise apply the product operations.
%
\begin{code}
_×SDP_ : SDProc → SDProc → SDProc
(SDP S₁ C₁ sf₁) ×SDP (SDP S₂ C₂ sf₂)
  = SDP (S₁ × S₂) (C₁ ×C C₂) (sf₁ ×sf sf₂)
\end{code}

\begin{figure}
\label{images:product}
\centering
\includegraphics[scale=0.7]{images/product.png}
\caption{Illustration of a product of two processes. The process holds components of both states and advances both simultaneously.}
\end{figure}

%
An observation to be made here is that in order for the new system to exist in any state, it has to hold components of both prior states.
%
This has the consequence that if one of the prior processes do not have any states, the new problem may never exist in a state either.
%
Similarly, if one of the components reaches a point where there are no available controls, and thus can not progress, the other component will not be able to progress either.
%

%include 2dexamples.lagda

%
Functional programmers will often find they are in need of a unit, e.g when using |reduce| or other frequently appearing constructs from the functional paradigm.
%
Naturally, it would be convenient to define units for the combinators described in this script.
%

%
What we are after is a process that will not carry any extra information, or rather one that can not alter the information it carries.
%
Recall that in order for the product of two states to exist in any state, both state spaces has to be inhabited.
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

\begin{figure}
\label{images:singleton}
\centering
\includegraphics[scale=0.7]{images/singleton.png}
\caption{Illustration of the singleton process. The subscript ₀ here is meant to indicate that the state remains the same when the process advances.}
\end{figure}

%
Taking the product of any process and the singleton process would produce a process where the only change of information during each step is that of the process which is not the singleton.
%
Of course, the other process could itself be the singleton process also.
%
In this case the only change in each step is exactly that of the singleton process, which is no change at all.
%

%-----------------------------------------------------------------------
\subsection{Coproduct}
\label{subsec:coproductseqdecproc}

%
Seeing how we could define the product of two processes, we are left wondering if we can compute the sum of two processes.
%
The approach is similar to that of the product case.
%

%
The control, here considered a predicate, is a predicate on the sum of the terms.
%
The inhabitants of this sum predicate is the sum of the inhabitants of the prior predicates.
%
\begin{code}
_⊎C_ :  {S₁ S₂ : Set}
     →  Pred S₁ → Pred S₂ → Pred (S₁ ⊎ S₂)
(C₁ ⊎C C₂) (inj₁ s₁)  = C₁ s₁
(C₁ ⊎C C₂) (inj₂ s₂)  = C₂ s₂
\end{code}
%
Calculating a new step function from two prior step functions is relatively straight forward.
%
The first input is the sum of the two terms.
%
Depending on which term the first argument belongs to, one of the prior step functions is applied to it and the second argument, the predicate on that term.
%
The result of the application is then injected into the sum type using the same injection as the input.
%
\begin{code}
_⊎sf_  :   {S₁ S₂ : Set}
       ->  {C₁ : Pred S₁} -> {C₂ : Pred S₂}
       ->  Step S₁ C₁ -> Step S₂ C₂
       ->  Step (S₁ ⊎ S₂) (C₁ ⊎C C₂)
(sf₁ ⊎sf sf₂) (inj₁ s₁) c₁  = inj₁ (sf₁ s₁ c₁)
(sf₁ ⊎sf sf₂) (inj₂ s₂) c₂  = inj₂ (sf₂ s₂ c₂)
\end{code}
%
The sum of two problems is now computed by applying the sum operators componentwise.
%
\begin{code}
_⊎SDP_ : SDProc → SDProc → SDProc
SDP S₁ C₁ sf₁ ⊎SDP SDP S₂ C₂ sf₂
  = SDP (S₁ ⊎ S₂) (C₁ ⊎C C₂) (sf₁ ⊎sf sf₂)
\end{code}

% \TODO{Perhaps split into two sub-images with an ``OR'' inbetween as text}

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
\label{images:coproduct}
\caption{The coproduct of two processes. The process will take the shape of either of the two alternatives, but never both or a mix of the two.}
\end{figure}

%
In the case of the product process the two prior processes were not entirely independent.
%
If one process could not progress the other process was affected in the sense that it too could not process further.
%
The sum of two processes keeps the two problems truly independent.
%
In fact, the coproduct of two processes will start progressing from some initial state, and depending on which injection is used the other process will never advance.

%
A process that acts as a unit to the coproduct combinator is the empty process.
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
Computing the coproduct of two processes and getting a process that evaluates either of the two, without actually considering the other process, leaves us wondering what this is useful for.
%
It would be more useful if we could jump between the two processes.
%
To do this, we first need to define a relation between states.
%
We define a relation on two terms, and define it to be a mapping from an inhabitant of one term to an inhabitant of the other.
%
\begin{code}
_⇄_ : (S₁ S₂ : Set) → Set
s₁ ⇄ s₂ = (s₁ -> s₂) × (s₂ -> s₁)
\end{code}
%
Combining the two predicates on the terms look similar to that of the coproduct case, when looking at the type.
%
However, instead of the new predicate being defined as either of the two prior ones, it is now |Maybe| either of the two previous ones.
%
The idea is that if the selected inhabitant from this predicate is Nothing, the process would like to yield in favour of the other process.
%
\begin{code}
_⊎C+_ :  {S₁ S₂ : Set}
      →  Pred S₁ → Pred S₂ → Pred (S₁ ⊎ S₂)
(C₁ ⊎C+ C₂) (inj₁ s₁) = Maybe (C₁ s₁)
(C₁ ⊎C+ C₂) (inj₂ s₂) = Maybe (C₂ s₂)
\end{code}
%
In order to combine two step functions we need two additional pieces of information.
%
We need one relation from one term to the other, as well as an opposite relation. % opposite är helt fel old här.
%
If the predicate of the step function is ever Nothing, we will use the relation to map the value of the current term to a value of the other term.
%
\TODO{Kanske en 3-ställig operator _<|_|>_ eller liknande? Om trassligt, låt bli, eller använd syntax directive för att kunna lägga <->-argumentet före alla Step}
\begin{code}
⊎sf+  :  {S₁ S₂ : Set}
      →  {C₁ : Pred S₁} → {C₂ : Pred S₂}
      →  (S₁ ⇄ S₂)
      →  Step S₁ C₁ → Step S₂ C₂
      →  Step (S₁ ⊎ S₂) (C₁ ⊎C+ C₂)
⊎sf+ _          sf₁ sf₂  (inj₁ s₁)  (just c)  = inj₁ (sf₁ s₁ c)
⊎sf+ _          sf₁ sf₂  (inj₂ s₂)  (just c)  = inj₂ (sf₂ s₂ c)
⊎sf+ (r₁ , _ )  sf₁ sf₂  (inj₁ s₁)  nothing   = inj₂ (r₁ s₁)
⊎sf+ (_  , r₂)  sf₁ sf₂  (inj₂ s₂)  nothing   = inj₁ (r₂ s₂)

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
\caption{Illustration of the yielding coproduct process. It is capable of switching between the two processes.}
\end{figure}

%
With a combinator such as this one you could describe e.g software.
%
As an example, one process could model the normal execution of some software, while the other could model the behaviour of an exception handler.
%
When the process modeling the software reaches a point where an exception is thrown, the process can yield control to the exception handler.
%
When the exception handler process is done, it will reach a state where it can yield in favour of the other process again.
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
The next combinator is one that interleaves processes, allowing each of the two prior processes to progress one step at a time each.
%
This behaviour could be similar to that of a game, where two players take turns making their next move.
%
However, the users do not know what moves the other player has made, and can therefore not make particularly smart moves.
%
In section -insert section with policies- it is shown how computing optimal policies produce controls which do know of the other users move.

%
Given two states, how can we produce a new state which not only captures all inhabitants of the separate states, but also knows which process should be allowed to advance next?
%
The most natural way seems to be to create a 3-ary product, where one of the components is an index indicating which of the two processes turn it is to advance.
%\TODO{Add format directiove to subscript S, etc. _\text{S}}
\begin{code}
_⇄S_ : Set → Set → Set
S₁ ⇄S S₂ = Fin 2 × S₁ × S₂
\end{code}
%
The predicate on this new state, defined in terms of the two previous predicates, is defined as follows.
%
If the value of the first component is zero, we select the first predicate.
%
If the value is one, we select the second predicate.
%
Agda require us to include a case for when the first component has any other value also, but quickly realises that this is an unreachable case.
%
\TODO{name for suc zero: one}
\begin{code}
one : Fin 2
one = suc zero

_⇄C_ :  {S₁ S₂ : Set}
     →  Pred S₁ → Pred S₂ → Pred (S₁ ⇄S S₂)
(C₁ ⇄C C₂) (zero , s₁ , s₂)      = C₁ s₁
(C₁ ⇄C C₂) (one , s₁ , s₂)  = C₂ s₂
\end{code}
%
The step function will inspect this first component and based on what value it has, it is going to invoke one of the prior step functions on the appropriate component.
%
The other component that is not the index is left unchanged, while the index is changed to indicate that the other process is the one to advance next.
%
\begin{code}
_⇄sf_  :  {S₁ S₂ : Set}
       →  {C₁ : Pred S₁} → {C₂ : Pred S₂}
       →  Step S₁ C₁ → Step S₂ C₂
       →  Step (S₁ ⇄S S₂) (C₁ ⇄C C₂)
(sf₁ ⇄sf sf₂) (zero , s₁ , s₂)      c  = (suc zero  , sf₁ s₁ c  , s₂        )
(sf₁ ⇄sf sf₂) (suc zero , s₁ , s₂)  c  = (zero      , s₁        , sf₂ s₂ c  )
(sf₁ ⇄sf sf₂) (suc (suc ()) , _)
\end{code}
Combining two processes to capture this interleaved behaviour is once again simply done by combining the components componentwise.
\begin{code}
_⇄SDP_ : SDProc → SDProc → SDProc
SDP S₁ C₁ sf₁ ⇄SDP SDP S₂ C₂ sf₂
  = SDP (S₁ ⇄S S₂) (C₁ ⇄C C₂) (sf₁ ⇄sf sf₂)
\end{code}

\begin{figure}
\label{images:interleave}
\centering
\includegraphics[scale=0.7]{images/interleave.png}
\caption{Illustration of two interleaved process. We want to emphasise that the state holds components of both prior states, but chooses to advance only one.}
\end{figure}

%
This way of modeling the interleaved problem is not optimal, as combining more than two processes with it will produce undesired behaviour.
%
If we combine three processes using this combinator the resulting system would be one where one of the processes advance half the time, and the other two only a quarter of the time each.
%

\TODO{Perhaps code up with i : FIn n times Vec n S or similar (don't bother with different S)}

\begin{figure}
\label{images:badinterleave}
\centering
\includegraphics[scale=0.7]{images/badinterleave.png}
\caption{If we interleave two processes, and then interleave the resulting process with a third we get a situation like this. They are not properly interleaved.}
\end{figure}

%
If we instead consider an implementation where the input to the combinator is a vector of processes, we would construct a more clever process with a better indexing behaviour.
%

\begin{figure}
\label{images:wantedinterleave}
\centering
\includegraphics[scale=0.7]{images/wantedinterleave.png}
\caption{This is the interleaved behaviour we would want for three processes.}
\end{figure}

%
A system like this would let all the processes advance equally much.
%
\TODO{implement this - A general product type with an indexing function}
%-----------------------------------------------------------------------
\begin{code}
⇄m : Set → ℕ → Set
⇄m S n = Fin n × Vec S n

⇄C : {S : Set} → {n : ℕ} → Vec (Pred S) n → Pred (⇄m S n)
⇄C c (index , states) = (lookup index c) (lookup index states)

--⇄sf : {S : Set} → {n : ℕ} → {C : Vec (Pred S) n} → {!!} → Step (⇄m S n) (⇄C C)
--⇄sf v = {!!}

--⇄SDP' : {n : ℕ} → Vec SDProc n → SDProc
--⇄SDP' {n} v = SDP (⇄m {!!} n) (⇄C {!!}) (⇄sf {!!})
\end{code}
