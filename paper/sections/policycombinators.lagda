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
Given policies for two individual processes, creating a policy for the product process is straightforward.
%
Given a state, the policy must return a control.
%
The control space for a product process is the product of the two separate control spaces.
%
\begin{code}
_×P_  :   {p₁ p₂ : SDProc}
      →   Policy p₁ → Policy p₂ → Policy (p₁ ×SDP p₂)
(p₁ ×P p₂) (fst , snd) = (p₁ fst , p₂ snd)
\end{code}
%
A policy for the sum of two processes is defined by pattern matching on the state.
%
If the pattern matches on the left injection, we can reuse the previous policy defined on that state.
%
Similarly, if the pattern matches on the right injection we can reuse the given policy for the other process.
%
\begin{code}
_⊎P_ :  {p₁ p₂ : SDProc} →
        Policy p₁ → Policy p₂ → Policy (p₁ ⊎SDP p₂)
p₁ ⊎P p₂ =   λ {  (inj₁  s₁) →  p₁  s₁;
                  (inj₂  s₂) →  p₂  s₂}
\end{code}
%
Reusing policies for the yielding coproduct is similar to that of the regular coproduct.
%
One difference is that in order to satisfy the Agda typechecker we need to also supply the swap functions that is used when combining the processes.
%
The only other difference is that when reusing the old policy the result must be wrapped in the |just| constructor.
%
\begin{code}
_⊎P+_  :  {p₁ p₂ : SDProc}
       →  Policy p₁ → Policy p₂
       →  (rel :  #st p₁  ⇄  #st p₂)
       →  Policy ((p₁ ⊎SDP+ p₂) rel)
(p₁ ⊎P+ p₂) rel =  λ {  (inj₁ s₁)  → just (p₁ s₁);
                        (inj₂ s₂)  → just (p₂ s₂)}
\end{code}
%
To combine two policies for the interleaved system we recall that the control space changes when the index changes.
%
When the index is 0 the control space is that of the first process, and when it is 1 the control space is that of the second process.
%
Similarly, in order to reuse the two previous policies we must then pattern match on the state and see what the index is.
%
If the index is |zero|, we reuse the first policy.
%
If it is |suc zero|, we reuse the other policy.
%
\begin{code}
_⇄P_  :  {p₁ p₂ : SDProc}
      →  Policy p₁ → Policy p₂ → Policy (p₁ ⇄SDP p₂)
p₁ ⇄P p₂ =
  λ { (zero , state)      → p₁ (proj₁ state);
      (suc zero , state)  → p₂ (proj₂ state);
      (suc (suc ()) , _)}
\end{code}

%
Now we come to the interesting bit.
%
If we have two policy sequences of equal length, we can compute a new policy sequence of the same length for a combination of the two previous processes.
%
We leverage Agdas typesystem to define a function that is as precise as possible, allowing us to pass the combinator as a parameter.
%
Then the defining equation of the function is a |zipWith|, applying the policy combinator pairwise on the two sequences.
%
\begin{code}
combineSeq  :  {p₁ p₂ : SDProc} {n : ℕ}
               {_:comb:_ : SDProc → SDProc → SDProc}
            →  (Policy p₁ → Policy p₂ → Policy (p₁ :comb: p₂))
            →  PolicySeq p₁ n → PolicySeq p₂ n → PolicySeq (p₁ :comb: p₂) n
combineSeq = zipWith

⊎↦× : (p₁ p₂ : SDProc) → Policy (p₁ ⊎SDP p₂) → Policy p₁ × Policy p₂
⊎↦× _ _ policy = (λ s₁ → policy (inj₁ s₁)) , λ s₂ → policy (inj₂ s₂)

×↦⊎ : (p₁ p₂ : SDProc) → Policy p₁ × Policy p₂ → Policy (p₁ ⊎SDP p₂)
×↦⊎ _ _ (p₁ , p₂) = λ { (inj₁ s₁) → p₁ s₁ ; (inj₂ s₂) → p₂ s₂}

∀⊎↦× : {p₁ p₂ : SDProc} → (p : Policy (p₁ ⊎SDP p₂)) → ×↦⊎ p₁ p₂ (⊎↦× p₁ p₂ p) ≡  p
∀⊎↦× {x} {y} p = {!!}
\end{code}
