% -*- Latex -*-
\section{Combinators for the Time Dependent Case}
\label{sec:combinatorstime}
%if false
\begin{code}
module combinatorstime where

open import core.seqdecproctime
open import combinators
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
We capture this by defining |TPred| to be a predicate on a predicate on ℕ.
%
The inhabitants of this type is a function that given a time |t|, returns a predicate on S applied to |t|, which is the way we modeled controls earlier.
%
\begin{code}
TPred : Pred ℕ → Set₁
TPred S = (t : ℕ) → Pred (S t)
\end{code}
%
Now on to the product combinator for the time dependent case.
%
To combine two predicates on natural numbers, two time dependent states, we return a new predicate on natural numbers that given a time |t| returns the product of applying the two predicates to |t|.
%
\begin{code}
_×St_ : (S₁ S₂ : Pred ℕ) → Pred ℕ
s₁ ×St s₂ = λ t → s₁ t × s₂ t
\end{code}
%
Combining two controls becomes the task of combining two |TPred|, and produce a new |TPred| on the result of applying |×St| to two predicates on natural numbers.
%
The result is a predicate that given a time and a state, applies the prior predicates to the time and the state componentwise.
%
\begin{code}
_×Ct_ : {S₁ S₂ : Pred ℕ} → TPred S₁ → TPred S₂ → TPred (S₁ ×St S₂)
s₁ ×Ct s₂ = λ time → λ state → s₁ time (proj₁ state) × s₂ time (proj₂ state)
\end{code}
%
Again we capture the type of the step function in a type |TStep|.
%
|TStep| accepts a state and a control, a predicate |S| on natural numbers and a predicate on |S|, and returns a type.
%
\begin{code}
TStep : (S : Pred ℕ) -> TPred S -> Set
TStep S C = (t : ℕ) → (s : S t) -> C t s -> S (suc t)
\end{code}
%
Combining two such step functions is similar to the time independent case.
%
The only different is that we have an extra parameter |time|, and we must apply the step functions to this |time| parameters.
%
\begin{code}
_×sft_ :  {S₁ S₂ : Pred ℕ} → {C₁ : TPred S₁} → {C₂ : TPred S₂}
      →  TStep S₁ C₁ → TStep S₂ C₂ → TStep (S₁ ×St S₂) (C₁ ×Ct C₂)
sf₁ ×sft sf₂ = λ time → λ state → λ control →
  sf₁ time (proj₁ state) (proj₁ control) , sf₂ time (proj₂ state) (proj₂ control)
\end{code}
%
Finally, combining two time dependent sequential decision processes is done by applying the combinators componentwise.
%
\begin{code}
_×SDPT_ : SDProcT → SDProcT → SDProcT
SDPT S₁ C₁ sf₁ ×SDPT SDPT S₂ C₂ sf₂ = SDPT (S₁ ×St S₂) (C₁ ×Ct C₂) (sf₁ ×sft sf₂)
\end{code}

%
the coproduct is similar to the product case, except that it returns the sum of applying to predicates to the time.
%
\begin{code}
_⊎St_ : (S₁ S₂ : Pred ℕ) → Pred ℕ
s₁ ⊎St s₂ = λ t → s₁ t ⊎ s₂ t
\end{code}
Combining two controls is done by pattern matching on the state and return one of the previous predicates applies to the time and the state.
\begin{code}
_⊎Ct_ : {S₁ S₂ : Pred ℕ} → TPred S₁ → TPred S₂ → TPred (S₁ ⊎St S₂)
(C₁ ⊎Ct C₂) time = λ {  (inj₁ s₁) → C₁ time s₁ ;
                         (inj₂ s₂) → C₂ time s₂}
\end{code}
%
Combining the step functions to produce one defined for the new process is, similarly to the time independent case, done by pattern matching on the state.
%
If the state is injected with the first injection, we apply the first step function, and similarly for the second injection.
%
\begin{code}
_⊎sft_ :  {S₁ S₂ : Pred ℕ} → {C₁ : TPred S₁} → {C₂ : TPred S₂}
       →  TStep S₁ C₁ → TStep S₂ C₂ → TStep (S₁ ⊎St S₂) (C₁ ⊎Ct C₂)
sf₁ ⊎sft sf₂ = λ time → λ {  (inj₁ s₁) → λ control → inj₁ (sf₁ time s₁ control) ;
                              (inj₂ s₂) → λ control → inj₂ (sf₂ time s₂ control)}
\end{code}
Again we combine two processes by applying the component combinators componentwise.
\begin{code}
_⊎SDPT_ : SDProcT → SDProcT → SDProcT
SDPT S₁ C₁ sf₁ ⊎SDPT SDPT S₂ C₂ sf₂ = SDPT (S₁ ⊎St S₂) (C₁ ⊎Ct C₂) (sf₁ ⊎sft sf₂)
\end{code}

%
To combine two time dependent processes into a yielding coproduct we begin by describing the component that relates the states in one process to states in the other.
%
\begin{code}
_⇄t_ : (S₁ S₂ : Pred ℕ) → Set -- change time parameter
s₁ ⇄t s₂ = ((t : ℕ) → s₁ t → s₂ (suc t)) × ((t : ℕ) → s₂ t → s₁ (suc t))
\end{code}
%
The first change from the coproduct combinator is again that the control space is extended to contain also the |nothing| constructor.
%
\begin{code}
_⊎Ctm_ : {S₁ S₂ : Pred ℕ} → TPred S₁ → TPred S₂ → TPred (S₁ ⊎St S₂)
C₁ ⊎Ctm C₂ = λ time → λ {  (inj₁ s₁) → Maybe (C₁ time s₁) ;
                            (inj₂ s₂) → Maybe (C₂ time s₂)}
\end{code}
%
In contrast to the coproduct case, the new step function will switch which process is executing if the control is the |nothing| constructor, and otherwise, depending on which injection was used, apply one of the previous step functions.
%
\begin{code}
⊎sftm : {S₁ S₂ : Pred ℕ} → {C₁ : TPred S₁} → {C₂ : TPred S₂} → S₁ ⇄t S₂ → TStep S₁ C₁ → TStep S₂ C₂ → TStep (S₁ ⊎St S₂) (C₁ ⊎Ctm C₂)
⊎sftm _         sf₁ sf₂ time (inj₁ s₁) (just c₁)  = inj₁ (sf₁ time s₁ c₁)
⊎sftm (r₁ , _)  sf₁ sf₂ time (inj₁ s₁) nothing    = inj₂ (r₁ time s₁)
⊎sftm _         sf₁ sf₂ time (inj₂ s₂) (just c₂)  = inj₂ (sf₂ time s₂ c₂)
⊎sftm (_ , r₂)  sf₁ sf₂ time (inj₂ s₂) nothing    = inj₁ (r₂ time s₂)
\end{code}
%
In the spirit of keeping notation similar, we provide a misfix operator for the step combinator.
%
\begin{code}
syntax ⊎sftm r sf₁ sf₂ = sf₁ ⟨ r ⟩ᵗ sf₂
\end{code}
%
To create a yielding coproduct we use the same combinator for the state space, but use the new modified combinators for the control space and step function.
%
\begin{code}
⊎SDPTm : (p₁ : SDProcT) → (p₂ : SDProcT) → (#stᵗ p₁) ⇄t (#stᵗ p₂) → SDProcT
⊎SDPTm (SDPT S₁ C₁ sf₁) (SDPT S₂ C₂ sf₂) r = SDPT (S₁ ⊎St S₂) (C₁ ⊎Ctm C₂) (sf₁ ⟨ r ⟩ᵗ sf₂)
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
-- TODO (perhaps) new Fin t state type for 1d example
\begin{code}
inv : Fin 2 -> Fin 2
inv zero        = suc zero
inv (suc zero)  = zero
inv (suc (suc ()))

double : (Fin 2 × ℕ) -> ℕ
double (zero , h) = 2 * h
double (one  , h) = suc (2 * h)

-- Spec: split (2*n) = (0, (n , n)); split (2*n+1) = (1, (n+1 , n))
split : ℕ -> Fin 2 × ℕ × ℕ
split 0 = (zero      , (0 , 0))
split 1 = (suc zero  , (1 , 0))
split (suc (suc n)) with split n
... | (r , (i₁ , i₂ )) = (inv r , (suc i₁ , suc i₂))

-- Spec: evenhalf (2*h+k) = (k, h) where k : Fin 2
evenhalf : ℕ -> Fin 2 × ℕ
evenhalf 0 = (zero      , 0)
evenhalf 1 = (suc zero  , 1)
evenhalf (suc (suc n)) with evenhalf n
... | (r , h) = (inv r , suc h)

evenhalfP : (n : ℕ) -> Σ (Fin 2 × ℕ) (\ri -> n ≡ double ri)  --  is this property right / enough?
evenhalfP 0 = ((zero      , 0) , refl)
evenhalfP 1 = ((suc zero  , 0) , refl)
evenhalfP (suc (suc n)) with evenhalfP n
... | ((r , h) , pr) = ((inv r , suc h) , {!!})

lemma2 :  (n : ℕ) -> (h : ℕ) ->
          (n ≡ 2 * h) -> (suc (suc n) ≡ 2 * (suc h))
lemma2 .(h + (h + 0)) h refl = cong suc {!!}

-- Goal: suc (suc (h + (h + zero))) ≡ suc (h + suc (h + zero))

lemmastep :  (n : ℕ) -> (r : Fin 2) -> (h : ℕ) ->
             (         n  ≡ double (r ,     h)) ->
             (suc (suc n) ≡ double (r , suc h))
lemmastep n zero     h  pr = {!!} -- lemma2 n h pr
lemmastep n (suc r)  h  pr = {!!}

lemma : {n : ℕ} -> (r : Fin 2) -> (h : ℕ)
 -> suc (suc (double (r , h))) ≡ double (r , suc h)
lemma zero    h = {!!} -- need to work with the definition of double
lemma (suc r) h = {!!}

mayadd : Fin 2 -> ℕ -> ℕ
mayadd zero   i = i
mayadd one    i = suc i

HelpS : Pred ℕ → Pred ℕ → Pred (Fin 2 × ℕ)
HelpS S₁ S₂ (r , i) = S₁ (mayadd r i) × S₂ i
-- The helper |mayadd| makes Agda see the the RHS is always a pair type.
-- S₁ i × S₂ i   or   S₁ (suc i) × S₂ i  depending on r

_⇄St_ : (S₁ S₂ : Pred ℕ) → Pred ℕ
(S₁ ⇄St S₂) t = HelpS S₁ S₂ (evenhalf t)

HelpC : {S₁ S₂ : Pred ℕ} → TPred S₁ → TPred S₂ → (ri : (Fin 2 × ℕ)) → Pred (HelpS S₁ S₂ ri)
HelpC C₁ C₂ (zero      , i) (s₁ , _ ) = C₁ i s₁
HelpC C₁ C₂ (suc zero  , i) (_  , s₂) = C₂ i s₂
HelpC C₁ C₂ (suc (suc ()) , _)

_⇄Ct_ : {S₁ S₂ : Pred ℕ} → TPred S₁ → TPred S₂ → TPred (S₁ ⇄St S₂)
(C₁ ⇄Ct C₂) t = HelpC C₁ C₂ (evenhalf t)
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

t == double ri =>


snd (evenhalf t) == snd (evenhalf (suc t))

    proj₁ (evenhalf time) == zero
  ->
    mayadd (evenhalf (suc time))  ~= suc time

\begin{code}

_⇄sft_ : {S₁ S₂ : Pred ℕ} → {C₁ : TPred S₁} → {C₂ : TPred S₂} → TStep S₁ C₁ → TStep S₂ C₂ → TStep (S₁ ⇄St S₂) (C₁ ⇄Ct C₂)
(sf₁ ⇄sft sf₂) time (s₁ , s₂) c with evenhalf time
... | (zero , i) = ({!S₁ (mayadd (evenhalf (suc time))) !} , {!!}) -- (sf₁ i s₁ c , s₂)
... | (one  , i) = ({!!} , {!!}) -- (s₁ , sf₂ i s₂ c)

{-
... | (zero , i) | (zero  , j)  = ({!!} , {!!})  -- impossible
... | (zero , i) | (suc r , j)  = ({!!} , {!s₂!}) -- (sf₁ {!i!} {!s₁!} {!c!} , {!s₂!})  --   proof needed of i == j
... | (one  , i) | (zero  , j)  = ({!s₁!} , {!sf₂ ? ? ?!})
... | (one  , i) | (suc r , j)  = ({!!} , {!!}) -- impossible
-}
\end{code}
-- , {!!} -- λ { (s₁ , s₂) → λ control → ({!!} , {!!}) }

we want to use
  sf1 : (i : T) -> (s1 : S1 i) -> C1 i s1 -> S1 (suc i)  -- at even times (inc. first  index, keep second constant)
  sf2 : (i : T) -> (s2 : S2 i) -> C2 i s2 -> S2 (suc i)  -- at odd  times (inc. second index, keep first  constant)
to move from  (s1 , s2)
  to (sf1 i s1 c , s2)
  or (s1, sf2 i s2 c)

Of type
  TStep (S₁ ⇄St S₂) (C₁ ⇄Ct C₂)
= -- TStep S C = (t : ℕ) → (s : S t) -> C t s -> S (suc t)
  (t : ℕ) → (s : (S₁ ⇄St S₂) t) -> (C₁ ⇄Ct C₂) t s -> (S₁ ⇄St S₂) (suc t)
=
  (t : ℕ) → (s : HelpS S₁ S₂ (evenhalf t)) -> (C₁ ⇄Ct C₂) t s -> HelpS S₁ S₂ (evenhalf (suc t))
