% -*- Latex -*-

\section{Policy Combinators}
\label{sec:policycombinators}

%
Now that we have a way of reusing sequential decision processes to create more sophisticated processes, we want to reuse existing policy sequences also.
%
As the function |trajectory|, which observes a process, accepts as input a process and a policy sequence, this would simplify combining and observing processes without having to write any new policy sequences.
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
First, let's consider how to combine individual policies, before we move on to policy sequences.
%

%
We redefine a policy to be a predicate on a state and a control.
%
\begin{code}
P : (S : Set) → (C : S → Set) → Set
P S C = (s : S) → C s
\end{code}
%
A policy for a product process is the product of the two individual policies.
%
\begin{code}
_×P_  :  {S₁ S₂ : Set} {C₁ : Pred S₁} {C₂ : Pred S₂}
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
_⊎P_  :  {S₁ S₂ : Set} {C₁ : Pred S₁} {C₂ : Pred S₂}
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
_⊎P+_  :  {S₁ S₂ : Set} {C₁ : Pred S₁} {C₂ : Pred S₂}
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
_⇄P_  :  {S₁ S₂ : Set} {C₁ : Pred S₁} {C₂ : Pred S₂}
      →  P S₁ C₁ → P S₂ C₂
      →  P (S₁ ⇄S S₂) (C₁ ⇄C C₂)
(p₁ ⇄P p₂) (zero , s₁ , _)      = p₁ s₁
(p₁ ⇄P p₂) (suc zero , _ , s₂)  = p₂ s₂
(p₁ ⇄P p₂) (suc (suc ()) , _)
\end{code}

\TODO{Maybe this should not be here? Just using zipWith and a combinator works fine, while using this gives yellow coloring.}
%
Now we come to the interesting bit.
%
If we have two policy sequences of equal length, we can compute a new policy sequence of the same length for a combination of the two previous processes.
%
The defining equation for the combinator is |zipWith|, which applies the policy combinator pairwise on the two sequences.
%
\begin{code}
combineSeq  :  {p₁ p₂ : SDProc} {n : ℕ}
               {_:comb:_ : SDProc → SDProc → SDProc}
            →  (Policy p₁ → Policy p₂ → Policy (p₁ :comb: p₂))
            →  PolicySeq p₁ n → PolicySeq p₂ n
            →  PolicySeq (p₁ :comb: p₂) n
combineSeq = zipWith
\end{code}
% \TODO{Should we keep these? Seems like we need more if we should keep these.}
With these combinators in place we observe that a policy for a coproduct process is a product of policies for the individual processes.
%
We show the translation as Agda functions.
%
\begin{code}
⊎↦×  :  {p₁ p₂ : SDProc} → Policy (p₁ ⊎SDP p₂)
     →  Policy p₁ × Policy p₂
⊎↦× policy = (  λ s₁ → policy (inj₁ s₁)) ,
                λ s₂ → policy (inj₂ s₂)

×↦⊎  :  {p₁ p₂ : SDProc} → Policy p₁ × Policy p₂
     →  Policy (p₁ ⊎SDP p₂)
×↦⊎ (p₁ , p₂) = λ {  (inj₁ s₁) → p₁ s₁ ;
                     (inj₂ s₂) → p₂ s₂}
\end{code}

% I am not sure how to show this? Is it possible if there are yellow markers?
\begin{code}
--∀⊎↦× : {p₁ p₂ : SDProc} → (p : Policy (p₁ ⊎SDP p₂)) → (state : #st (p₁ ⊎SDP p₂)) → ×↦⊎ (⊎↦× p) state ≡  p state
--∀⊎↦× {x} {y} p state = {!!}
\end{code}
