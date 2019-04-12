\begin{code}

module Bellman where

open import Data.Nat
open import Agda.Builtin.Nat using (_==_; _+_)
open import Data.Bool hiding (_∨_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_; inj₁ to inl; inj₂ to inr)
open import Data.Maybe
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Vec

open import SeqDecProc
open import SeqDecProb

data So : Bool → Set where
  oh : So true

_leq_ : ℕ → ℕ → Bool
zero leq n = true
suc m leq zero = false
suc m leq suc n = m leq n

data CtrlSeq : (x : SeqDecProb) → getstate x → ℕ → Set where
    nil : (x : SeqDecProb) → (state : getstate x) → CtrlSeq x state zero
    _∷_ : {n : ℕ} → (x : SeqDecProb) →
           (state : getstate x)            →
           (y : getcontrol x state)        →
           CtrlSeq x (getstep x state y) n →
           CtrlSeq x state (suc n)

value : {n : ℕ} → (x : SeqDecProb) → (state : getstate x) → CtrlSeq x state n → ℕ
value x state (nil .x .state) = 0
value x state ((.x ∷ .state) y seq) =
  getreward x state y (getstep x state y) +
  value x (getstep x state y) seq
  
OptCtrlSeq : {n : ℕ} → (x : SeqDecProb) → (state : getstate x) → CtrlSeq x state n → Set
OptCtrlSeq x state seq =
  {n : ℕ} → (ys : CtrlSeq x state n) → So (value x state ys leq value x state seq)
  
PolicyP : (x : SeqDecProb) →  Set
PolicyP (SDProb state control step val reward) = (x : state) → control x

PolicyPSeq : SeqDecProb → ℕ → Set
PolicyPSeq x n = Vec (PolicyP x) n

val : {n : ℕ} → (x : SeqDecProb) → (state : getstate x) → PolicyPSeq x n → ℕ
val x state [] = 0
val x state (x₁ ∷ seq) = getreward x state (x₁ state) x' + val x x' seq
  where x' : getstate x
        x' = getstep x state (x₁ state)

OptPolicyPSeq : {n : ℕ} → (x : SeqDecProb) → PolicyPSeq x n → Set
OptPolicyPSeq x seq = {n : ℕ}                →
                      (state : getstate x)   →
                      (ps' : PolicyPSeq x n) →
                      So (val x state ps' leq val x state seq)

OptExt : {n : ℕ} → (x : SeqDecProb) → PolicyPSeq x n → PolicyP x → Set
OptExt x seq p = (p' : PolicyP x)     →
                   (state : getstate x) →
                   So (val x state (p' ∷ seq) leq val x state (p ∷ seq))

{- Given a state and a function which from controls available in that state computes
   a value (reward), returns the maximum of therese rewards obtainable.
   How to 'terate' over all possible controls? -}
max : (x : SeqDecProb) → (state : getstate x) → (getcontrol x state → ℕ) → ℕ
max x state f = {!!}

{- Similarly to max, computes based on the same principle, but returns the argument (control)
   that produced this maximum reward. -}
argmax : (x : SeqDecProb) → (state : getstate x) → (getcontrol x state → ℕ) → getcontrol x state
argmax x state f = {!!}

MaxSpec : Set₁
MaxSpec = (x : SeqDecProb) → (state : getstate x) → (f : getcontrol x state → ℕ) →
          (y : getcontrol x state) → So (f y leq max x state f)

ArgmaxSpec : Set₁
ArgmaxSpec = (x : SeqDecProb) → (state : getstate x) → (f : getcontrol x state → ℕ) → So (f (argmax x state f) == max x state f)

optExt : {n : ℕ} → (x : SeqDecProb) → PolicyPSeq x n → PolicyP x
optExt x ps state = argmax x state f
  where f : getcontrol x state → ℕ
        f y = getreward x state y (getstep x state y) +
              val x (getstep x state y) ps
    
OptExtLemma : {n : ℕ} → (x : SeqDecProb) → (ps : PolicyPSeq x n) → OptExt x ps (optExt x ps)
OptExtLemma x ps p' state = {!!}

backwardsInduction : (n : ℕ) → (x : SeqDecProb) → PolicyPSeq x n
backwardsInduction zero x = []
backwardsInduction (suc n) x = (optExt x ps) ∷ ps
  where ps : PolicyPSeq x n
        ps = backwardsInduction n x

transitiveLTE : (x₁ x₂ x₃ : ℕ) → So (x₁ leq x₂) → So (x₂ leq x₃) → So (x₁ leq x₃)
transitiveLTE zero zero zero p₁ p₂ = oh
transitiveLTE zero zero (suc z) p₁ p₂ = oh
transitiveLTE zero (suc y) zero p₁ p₂ = oh
transitiveLTE zero (suc y) (suc z) p₁ p₂ = oh
transitiveLTE (suc x) zero zero () p₂
transitiveLTE (suc x) zero (suc z) () p₂
transitiveLTE (suc x) (suc y) zero p₁ ()
transitiveLTE (suc x) (suc y) (suc z) p₁ p₂ = transitiveLTE x y z p₁ p₂

monotonePlus : (x y : ℕ) → (z : ℕ) → So (x leq y) → So ((z + x) leq (z + y))
monotonePlus x y z p = {!-too lazy to complete now-!}

Bellman : {n : ℕ}                →
          (x : SeqDecProb)       →
          (ps : PolicyPSeq x n)  →
          (OptPolicyPSeq x ps)   →
          (p : PolicyP x)        →
          OptExt x ps p          →
          OptPolicyPSeq x (p ∷ ps)
Bellman x ps ops p oep = opps
  where opps : OptPolicyPSeq x (p ∷ ps)
        opps state []          = {!!}
        opps state (p' ∷ ps') = transitiveLTE (val x state (p' ∷ ps'))
                                               (val x state (p' ∷ ps))
                                               (val x state (p ∷ ps))
                                               step2
                                               step3
          where step1 : So (val x (getstep x state (p' state)) ps' leq val x (getstep x state (p' state)) ps)
                step1 = ops (getstep x state (p' state)) ps'
                step2 : So (val x state (p' ∷ ps') leq val x state (p' ∷ ps))
                step2 = monotonePlus (val x (getstep x state (p' state)) ps')
                                     (val x (getstep x state (p' state)) ps)
                                     (getreward x state (p' state)
                                     (getstep x state (p' state))) step1
                step3 : So (val x state (p' ∷ ps) leq val x state (p ∷ ps))
                step3 = oep p' state

\end{code}
