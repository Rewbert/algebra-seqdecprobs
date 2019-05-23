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
We redefine a policy to be a predicate on a state and a control.
%
\begin{code}
P : (S : Set) → (C : S → Set) → Set
P S C = (s : S) → C s
\end{code}
%
A policy for a product process defined in terms of two policies for the individual processes, is created by taking a pair of the two previous policies applied to the components of the state.
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
_⇄P_  :  {S₁ S₂ : Set}
          {C₁ : Pred S₁} {C₂ : Pred S₂}
      →  P S₁ C₁ → P S₂ C₂
      →  P (S₁ ⇄S S₂) (C₁ ⇄C C₂)
(p₁ ⇄P p₂) (zero , s₁ , _)      = p₁ s₁
(p₁ ⇄P p₂) (suc zero , _ , s₂)  = p₂ s₂
(p₁ ⇄P p₂) (suc (suc ()) , _)
\end{code}

%
With these policy combinators defined, we make a few observations.
%
We recall the claim that in an interleaved process the two prior processes does not know what state the other process is in.
%
It does not know what moves it has made.
%
The combinator above does indeed not inspect the other states component before applying the policy.
%
If we write new policies we can of course look at this parameter also.
%
The state of an interleaved process is a product, and we recall that by curring |(a,b) → c| is the same as |a → b → c|.
%
Consider |a| to be one processes state and |b| to be the others, we reason that a policy for the interleaved process is something like a policy for one of the processes parameterised over the other process.
%

% \TODO{Should we keep these? Seems like we need more if we should keep these.}
Another interesting observation to make is that a policy for a process with a sum state, e.g a policy for a coproduct, is a pair of policies for the separate processes.
%
We can make this concrete with the following two definitions.
%
\begin{code}
module test where
  ⊎↦×  : {S₁ S₂ : Set} {C₁ : Pred S₁} {C₂ : Pred S₂}
       →  P (S₁ ⊎ S₂) (C₁ ⊎C C₂)
       →  P S₁ C₁ × P S₂ C₂
  ⊎↦× policy = (  λ s₁ → policy (inj₁ s₁)) ,
                  λ s₂ → policy (inj₂ s₂)

  ×↦⊎  :  {S₁ S₂ : Set} {C₁ : Pred S₁} {C₂ : Pred S₂}
       →  P S₁ C₁ × P S₂ C₂
       →  P (S₁ ⊎ S₂) (C₁ ⊎C C₂)
  ×↦⊎ (p₁ , p₂) = λ {  (inj₁ s₁) → p₁ s₁ ;
                       (inj₂ s₂) → p₂ s₂}

  ∀⊎↦×  :  {S₁ S₂ : Set} {C₁ : Pred S₁} {C₂ : Pred S₂}
            (p : P (S₁ ⊎ S₂) (C₁ ⊎C C₂)) → (state : S₁ ⊎ S₂) →
            ×↦⊎ (⊎↦× p) state ≡  p state
  ∀⊎↦× _ (inj₁ _) = refl
  ∀⊎↦× _ (inj₂ _) = refl

⊎↦×  :  {p₁ p₂ : SDProc}
     →  Policy (p₁ ⊎SDP p₂)
     →  Policy p₁ × Policy p₂
⊎↦× policy = (  λ s₁ → policy (inj₁ s₁)) ,
                λ s₂ → policy (inj₂ s₂)

×↦⊎  :  {p₁ p₂ : SDProc}
     →  Policy p₁ × Policy p₂
     →  Policy (p₁ ⊎SDP p₂)
×↦⊎ (p₁ , p₂) = λ {  (inj₁ s₁) → p₁ s₁ ;
                     (inj₂ s₂) → p₂ s₂}
\end{code}

\begin{code}
∀⊎↦×  :  {p₁ p₂ : SDProc} →
          (p : Policy (p₁ ⊎SDP p₂)) → (state : #st (p₁ ⊎SDP p₂)) →
          ×↦⊎ {p₁} {p₂} (⊎↦× {p₁} {p₂} p) state ≡  p state
∀⊎↦× _ (inj₁ _) = refl
∀⊎↦× _ (inj₂ _) = refl

\end{code}
