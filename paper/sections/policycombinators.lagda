% -*- Latex -*-

\section{Policy Combinators}
\label{sec:policycombinators}

%
Now that we have a way of reusing sequential decision processes to create more sophisticated processes, we want to reuse existing policy sequences also.
%
As the function |trajectory| which observes a process accepts a process and a policy sequence as input, this would simplify combining and observing processes without having to write any new policy sequences.
%
%if false
\begin{code}
open import core.seqdecproc
open import combinators
open import Data.Product
open import Data.Sum
open import Data.Maybe using (just) -- hiding zipWith
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality
\end{code}
%endif
%
We start by combining single policies.
%

%
We remind the reader that a policy is defined in terms of a state and a control.
%
\begin{code}
P : (S : Set) → (C : S → Set) → Set
P S C = (s : S) → C s
\end{code}
%
A policy for a product process defined in terms of two policies for the individual processes, is created by taking a pair of the two previous policies applied to the components of the state.
%
%if False
\begin{code}
_×C_ : {S₁ S₂ : Set} (C₁ : Con S₁) (C₂ : Con S₂) → Con (S₁ × S₂)
(C₁ ×C C₂) (s₁ , s₂) = C₁ s₁ × C₂ s₂
\end{code}
%endif
\begin{code}
_×P_  :  {S₁ S₂ : Set} {C₁ : Con S₁} {C₂ : Con S₂}
      →  P S₁ C₁ → P S₂ C₂
      →  P (S₁ × S₂) (C₁ ×C C₂)
(p₁ ×P p₂) (s₁ , s₂) = p₁ s₁ , p₂ s₂
\end{code}
%
A policy for the sum of two processes is defined by pattern matching on the state.
%
If the pattern matches on the left injection, we can reuse the previous policy defined on that state.
%
Similarly, if the pattern matches on the right injection we can reuse the given policy for the other process.
%
\begin{code}
_⊎P_  :  {S₁ S₂ : Set} {C₁ : Con S₁} {C₂ : Con S₂}
      →  P S₁ C₁ → P S₂ C₂
      →  P (S₁ ⊎ S₂) (C₁ ⊎C C₂)
(p₁ ⊎P p₂) (inj₁ s₁) = p₁ s₁
(p₁ ⊎P p₂) (inj₂ s₂) = p₂ s₂
\end{code}
%
Reusing policies for the yielding coproduct is similar to that of the regular coproduct.
%
The only difference is that when reusing the old policy the result must be wrapped in the |just| constructor.
%
\begin{code}
_⊎P+_  :  {S₁ S₂ : Set} {C₁ : Con S₁} {C₂ : Con S₂}
       →  P S₁ C₁ → P S₂ C₂
       →  P (S₁ ⊎ S₂) (C₁ ⊎C+ C₂)
(p₁ ⊎P+ p₂) (inj₁ s₁) = just (p₁ s₁)
(p₁ ⊎P+ p₂) (inj₂ s₂) = just (p₂ s₂)
\end{code}
%
To combine two policies for an interleaved process we recall that the control space changes when the index changes.
%
When the index is 0 the control space is that of the first process, and when it is 1 the control space is that of the second process.
%
Similarly, in order to reuse the two previous policies we must then pattern match on the state and see what the index is.
%
If the index is |zero|, we reuse the first policy.
%
If it is |suc zero|, we reuse the second policy.
%
\begin{code}
_⇄P_  :  {S₁ S₂ : Set}
          {C₁ : Con S₁} {C₂ : Con S₂}
      →  P S₁ C₁ → P S₂ C₂
      →  P (S₁ ⇄S S₂) (C₁ ⇄C C₂)
(p₁ ⇄P p₂) (zero , s₁ , _)      = p₁ s₁
(p₁ ⇄P p₂) (suc zero , _ , s₂)  = p₂ s₂
(p₁ ⇄P p₂) (suc (suc ()) , _)
\end{code}

\section{A note on Policies}
\label{sec:anoteonpolicies}
%
With these policy combinators defined, we make a few observations.
%
These observations intend to illustrate some of the meanings behind policies.
%
\subsection{Product State Policies}
\label{subsec:productstatepolicies}
%
Recall a policy for a product state.
%
The type of this policy is |(s : State) → Control s|, where State is the type of states and Control is the type family of controls.
%
Since |s| is a product , the signature actually is something like |((a , b) : A × B) → Control (a , b)|.
%
We know from currying that this is the same as |(a : A) → (b : B) → Control (a , b)|.
%

%
In the case of the product combinator the control space was the product of the separate state components control spaces.
%
Where a policy for the individual process would base the choice of control on the state, the policy for a product process will select a control for the same state component, but base the choice on both state components.
%

%
In the case of the interleaved process we related the situation to that of a game, where players take turns making their moves.
%
In such a scenario a policy could be something of a game leader, making the best choices for each component based both components.
%
The policy can, after all, make a decision for one of the components based on the state of both components.
%

\subsection{Sum state implies Product Policy}
\label{subsec:sumstateimpliesproductpolicy}
Another interesting observation to make is that a policy for a process with a sum state, e.g a policy for a coproduct, is a pair of policies for the separate processes.
%
We can make this concrete with the following two definitions.
%
\begin{code}
⊎↦×  :  {S₁ S₂ : Set}
        {C₁ : Con S₁} {C₂ : Con S₂}
     →  P (S₁ ⊎ S₂) (C₁ ⊎C C₂)
     →  P S₁ C₁ × P S₂ C₂
⊎↦× policy = (  λ s₁ → policy (inj₁ s₁)) ,
                λ s₂ → policy (inj₂ s₂)

×↦⊎  :  {S₁ S₂ : Set}
        {C₁ : Con S₁} {C₂ : Con S₂}
     →  P S₁ C₁ × P S₂ C₂
     →  P (S₁ ⊎ S₂) (C₁ ⊎C C₂)
×↦⊎ (p₁ , p₂) = λ {  (inj₁ s₁) → p₁ s₁ ;
                     (inj₂ s₂) → p₂ s₂}
\end{code}
%
Then we can further solidify this statement by showing that they are equal by functional extensionality.
%
\begin{code}
∀⊎↦×  :  {S₁ S₂ : Set}
         {C₁ : Con S₁} {C₂ : Con S₂}
         (p : P (S₁ ⊎ S₂) (C₁ ⊎C C₂))
      →  (state : S₁ ⊎ S₂)
      →  ×↦⊎ (⊎↦× p) state ≡  p state
∀⊎↦× _ (inj₁ _) = refl
∀⊎↦× _ (inj₂ _) = refl
\end{code}
\TODO{formatters for these}
