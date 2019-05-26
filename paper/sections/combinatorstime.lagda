% -*- Latex -*-
\subsection{Combinators for the Time Dependent Case}
\label{subsec:combinatorstime}
%if false
\begin{code}
module combinatorstime where

open import core.seqdecproctime
open import combinators using (Pred)
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Maybe
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality
\end{code}
%endif
%
Before we move on we want to highlight that the state now is a predicate on the natural numbers.
%
The controls of these time dependent processes can be seen as a predicate on those natural number predicates.
%
We capture this reasoning in the definition of |Pred'|.
%
\begin{code}
Pred' : Pred ℕ → Set₁
Pred' S = (t : ℕ) → Pred (S t)
\end{code}
%
Now on to the product combinator for the time dependent case.
%
To combine two predicates on natural numbers, two time dependent states, we return a new predicate on natural numbers that given a time |t| returns the product of applying the two predicates to |t|.
%
\begin{code}
_×S_ : (S₁ S₂ : Pred ℕ) → Pred ℕ
s₁ ×S s₂ = λ t → s₁ t × s₂ t
\end{code}
%
The product combinator for two controls should produce a new |Pred'| on |S₁ ×S S₂| defined in terms of two predicates |Pred' S₁| and |Pred' S₂|.
%
The defining equation is similar to the time independent case, but the extra parameter time is given as the first argument.
%
\begin{code}
_×C_  :   {S₁ S₂ : Pred ℕ}
      →     Pred' S₁ → Pred' S₂   →  Pred' (S₁ ×S S₂)
(C₁ ×C C₂) time (s₁ , s₂) = C₁ time s₁ × C₂ time s₂
\end{code}
%
Again we capture the type of the step function in a type |Step|.
%
|Step| accepts a state and a control, a predicate |S| on natural numbers and a predicate on |S|, and returns a type.
%
\begin{code}
Step : (S : Pred ℕ) -> Pred' S -> Set
Step S C = (t : ℕ) → (s : S t) -> C t s -> S (suc t)
\end{code}
%
Combining two such step functions is similar to the time independent case.
%
The only different is that we have an extra parameter |time|, and we must apply the step functions to this |time| parameters.
%
\begin{code}
_×sf_  :  {S₁ S₂ : Pred ℕ}
       →  {C₁ : Pred' S₁} → {C₂ : Pred' S₂}
       →  Step S₁ C₁ → Step S₂ C₂
       →  Step (S₁ ×S S₂) (C₁ ×C C₂)
(sf₁ ×sf sf₂) time state control
  =  sf₁ time (proj₁ state) (proj₁ control) ,
     sf₂ time (proj₂ state) (proj₂ control)
\end{code}
%
Finally, combining two time dependent sequential decision processes is done by applying the combinators componentwise.
%
\begin{code}
_×SDP_ : SDProcT → SDProcT → SDProcT
SDPT S₁ C₁ sf₁ ×SDP SDPT S₂ C₂ sf₂
  = SDPT (S₁ ×S S₂) (C₁ ×C C₂) (sf₁ ×sf sf₂)
\end{code}
%
Just as the product combinator, the defining equation for the coproduct combinator is similar to its time independent counterpart.
%
The difference is again that the parameters are applied to the time.
%
\begin{code}
_⊎S_ : (S₁ S₂ : Pred ℕ) → Pred ℕ
s₁ ⊎S s₂ = λ t → s₁ t ⊎ s₂ t
\end{code}
%
The time dependent sum combinator for controls pattern matches on what injection was used, and applies the associated control to the time and the state.
%
\begin{code}
_⊎C_  :  {S₁ S₂ : Pred ℕ}
      →  Pred' S₁ → Pred' S₂ → Pred' (S₁ ⊎S S₂)
(C₁ ⊎C C₂) time = λ {  (inj₁ s₁) → C₁ time s₁ ;
                       (inj₂ s₂) → C₂ time s₂}
\end{code}
%
Combining the step functions to produce one defined for the new process is, similarly to the time independent case, done by pattern matching on the state.
%
If the state is injected with the first injection, we apply the first step function, and similarly for the second injection.
%
\begin{code}
_⊎sf_  :  {S₁ S₂ : Pred ℕ}
       →  {C₁ : Pred' S₁} → {C₂ : Pred' S₂}
       →  Step S₁ C₁ → Step S₂ C₂
       →  Step (S₁ ⊎S S₂) (C₁ ⊎C C₂)
(sf₁ ⊎sf sf₂) time (inj₁ s₁) c = inj₁ (sf₁ time s₁ c)
(sf₁ ⊎sf sf₂) time (inj₂ s₂) c = inj₂ (sf₂ time s₂ c)
\end{code}
Again we combine two processes by applying the component combinators componentwise.
\begin{code}
_⊎SDP_ : SDProcT → SDProcT → SDProcT
SDPT S₁ C₁ sf₁ ⊎SDP SDPT S₂ C₂ sf₂
  = SDPT (S₁ ⊎S S₂) (C₁ ⊎C C₂) (sf₁ ⊎sf sf₂)
\end{code}

%
To combine two time dependent processes into a yielding coproduct we begin by describing the component that relates the states in one process to states in the other.
%
\begin{code}
_⇄_ : (S₁ S₂ : Pred ℕ) → Set
s₁ ⇄ s₂ =  ((t : ℕ) → s₁ t → s₂ (suc t)) ×
           ((t : ℕ) → s₂ t → s₁ (suc t))
\end{code}
%
The first change from the coproduct combinator is again that the control space is extended to contain also the |nothing| constructor.
%
\begin{code}
_⊎C+_  :  {S₁ S₂ : Pred ℕ}
       →  Pred' S₁ → Pred' S₂ → Pred' (S₁ ⊎S S₂)
(C₁ ⊎C+ C₂) time (inj₁ s₁) = Maybe (C₁ time s₁)
(C₁ ⊎C+ C₂) time (inj₂ s₂) = Maybe (C₂ time s₂)
\end{code}
%
In contrast to the coproduct case, the new step function will switch which process is executing if the control is the |nothing| constructor, and otherwise, depending on which injection was used, apply one of the previous step functions.
%
\begin{code}
⊎sf+  :  {S₁ S₂ : Pred ℕ}
      →  {C₁ : Pred' S₁} → {C₂ : Pred' S₂} → S₁ ⇄ S₂
      →  Step S₁ C₁ → Step S₂ C₂
      →  Step (S₁ ⊎S S₂) (C₁ ⊎C+ C₂)
⊎sf+ _         sf₁ sf₂ time (inj₁ s₁) (just c₁)  =
  inj₁ (sf₁ time s₁ c₁)
⊎sf+ (r₁ , _)  sf₁ sf₂ time (inj₁ s₁) nothing    =
  inj₂ (r₁ time s₁)
⊎sf+ _         sf₁ sf₂ time (inj₂ s₂) (just c₂)  =
  inj₂ (sf₂ time s₂ c₂)
⊎sf+ (_ , r₂)  sf₁ sf₂ time (inj₂ s₂) nothing    =
  inj₁ (r₂ time s₂)
\end{code}
%
Again we provide an infix operator to be consistent.
%
\begin{code}
syntax ⊎sf+ r sf₁ sf₂ = sf₁ ⟨ r ⟩ sf₂
\end{code}
%
To create a yielding coproduct we use the same combinator for the state space, but use the new modified combinators for the control space and step function.
%
\begin{code}
⊎SDP+  :  (p₁ p₂ : SDProcT) →  (#st p₁) ⇄ (#st p₂)
       →  SDProcT
⊎SDP+ (SDPT S₁ C₁ sf₁) (SDPT S₂ C₂ sf₂) r
  = SDPT (S₁ ⊎S S₂) (C₁ ⊎C+ C₂) (sf₁ ⟨ r ⟩ sf₂)
\end{code}

%
When we try to implement the interleaved combinator for the time dependent case we run into some problems.
%
The main problem is that since the step function only advances one of the state components, the other one will be of the wrong type.
%
At time |n| one of the components get advanced to a state in time |suc n|, while the other is not changed at all.
% TODO @patrikja is this a thing, with several appendixes?
This problem is discussed further in Appendix B.
%
