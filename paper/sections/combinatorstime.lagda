% -*- Latex -*-
\section{Combinators for the Time Dependent Case}
\label{sec:combinatorstime}
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
Before we begin presenting the actual combinators we highlight that the state now is actually a predicate on the natural numbers.
%
The combinators of time dependent processes are now predicates on these time dependent predicates instead.
%
We capture this by defining |Pred'| to be a predicate on a predicate on ℕ.
%
The inhabitants of this type is a function that given a time |t|, returns a predicate on S applied to |t|, which is the way we modeled controls earlier.
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
Combining two controls becomes the task of combining two |Pred'|, and produce a new |Pred'| on the result of applying |×St| to two predicates on natural numbers.
%
The result is a predicate that given a time and a state, applies the prior predicates to the time and the state componentwise.
%
\begin{code}
_×C_ :  {S₁ S₂ : Pred ℕ} → Pred' S₁ → Pred' S₂
   →    Pred' (S₁ ×S S₂)
(s₁ ×C s₂) time state
  = s₁ time (proj₁ state) × s₂ time (proj₂ state)
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
_×sf_ :  {S₁ S₂ : Pred ℕ}
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
the coproduct is similar to the product case, except that it returns the sum of applying to predicates to the time.
%
\begin{code}
_⊎S_ : (S₁ S₂ : Pred ℕ) → Pred ℕ
s₁ ⊎S s₂ = λ t → s₁ t ⊎ s₂ t
\end{code}
Combining two controls is done by pattern matching on the state and return one of the previous predicates applies to the time and the state.
\begin{code}
_⊎C_ :  {S₁ S₂ : Pred ℕ} → Pred' S₁
     →  Pred' S₂ → Pred' (S₁ ⊎S S₂)
(C₁ ⊎C C₂) time = λ {  (inj₁ s₁) → C₁ time s₁ ;
                       (inj₂ s₂) → C₂ time s₂}
\end{code}
%
Combining the step functions to produce one defined for the new process is, similarly to the time independent case, done by pattern matching on the state.
%
If the state is injected with the first injection, we apply the first step function, and similarly for the second injection.
%
\begin{code}
_⊎sf_ :  {S₁ S₂ : Pred ℕ}
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
_⊎C+_ :  {S₁ S₂ : Pred ℕ}
      →  Pred' S₁ → Pred' S₂ → Pred' (S₁ ⊎S S₂)
(C₁ ⊎C+ C₂) time (inj₁ s₁) = Maybe (C₁ time s₁)
(C₁ ⊎C+ C₂) time (inj₂ s₂) = Maybe (C₂ time s₂)
\end{code}
%
In contrast to the coproduct case, the new step function will switch which process is executing if the control is the |nothing| constructor, and otherwise, depending on which injection was used, apply one of the previous step functions.
%
\begin{code}
⊎sf+ :  {S₁ S₂ : Pred ℕ}
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
In the spirit of keeping notation similar, we provide a misfix operator for the step combinator.
%
\begin{code}
syntax ⊎sf+ r sf₁ sf₂ = sf₁ ⟨ r ⟩ sf₂
\end{code}
%
To create a yielding coproduct we use the same combinator for the state space, but use the new modified combinators for the control space and step function.
%
\begin{code}
⊎SDP+ :  (p₁ p₂ : SDProcT) →  (#st p₁) ⇄ (#st p₂)
     →   SDProcT
⊎SDP+ (SDPT S₁ C₁ sf₁) (SDPT S₂ C₂ sf₂) r
  = SDPT (S₁ ⊎S S₂) (C₁ ⊎C+ C₂) (sf₁ ⟨ r ⟩ sf₂)
\end{code}

%

%if false
\begin{code}
-- rem when div with 2
rem : ℕ → ℕ
rem 0              = 0
rem 1              = 1
rem (suc (suc n))  = rem n

half : ℕ → ℕ
half n = ⌊ n /2⌋
\end{code}

  0  ->  1  ->  2  ->  3  ->  4  ->
(0,0)->(1,0)->(1,1)->(2,1)->(2,2)->...

%endif
\begin{code}
_⇄S_ : (S₁ S₂ : Pred ℕ) → Pred ℕ
s₁ ⇄S s₂ = λ t → s₁ (half t + rem t) × s₂ (half t)
\end{code}

\begin{code}
_⇄C_ : {S₁ S₂ : Pred ℕ} → Pred' S₁ → Pred' S₂ → Pred' (S₁ ⇄S S₂)
C₁ ⇄C C₂ = λ time → λ {  s₁×s₂  → C₁ (half time + rem time)  (proj₁ s₁×s₂) ;
                            s₁×s₂  → C₂ (half time)             (proj₂ s₁×s₂)}

-- Do we mean something like this for the control? The control above will never
-- suit the second component.
_⇄CC_ : {S₁ S₂ : Pred ℕ} → Pred' S₁ → Pred' S₂ → Pred' (S₁ ⇄S S₂)
(C₁ ⇄CC C₂) time (s₁ , s₂) with rem time | inspect rem time
(C₁ ⇄CC C₂) time (s₁ , s₂) | zero     | p  = C₁ (half time + zero) s₁
(C₁ ⇄CC C₂) time (s₁ , s₂) | suc rem  | p  = C₂ (half time) s₂
\end{code}
%
When we try to combine the two step functions we run into some trouble.
%
We can not actually do this.
%
The way we chose to define the state, such that it contains components of both processes with the intention of only allowing one component to change in each step, is suboptimal.
%
The step function must take the state at time |t| to a state at time |suc t|.
%
Given that the state space at time |suc t| might not be the same as at time |t|, we can not just leave the component the way it is.
%
\begin{code}
_⇄sf_ :  {S₁ S₂ : Pred ℕ} → {C₁ : Pred' S₁} → {C₂ : Pred' S₂}
      →  Step S₁ C₁ → Step S₂ C₂ → Step (S₁ ⇄S S₂) (C₁ ⇄CC C₂)
(sf₁ ⇄sf sf₂) time (s₁ , s₂) c with rem time | inspect rem time
(sf₁ ⇄sf sf₂) time (s₁ , s₂) c | zero | p = {!!} , {!s₂!}
(sf₁ ⇄sf sf₂) time (s₁ , s₂) c | one  | p = {!!} , {!!}

\end{code}
