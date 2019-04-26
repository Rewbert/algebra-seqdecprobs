\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module Bellman where

open import Data.Nat
open import Agda.Builtin.Nat using (_==_; _+_)
open import Data.Bool hiding (_∨_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_; inj₁ to inl; inj₂ to inr)
open import Data.Maybe
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Vec hiding (foldl; head)
open import Data.List


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

{- In order to implement max we need to specify an additional piece of information, namely
   how to iterate over all possible controls for a given state. An assumption is made
   about having this knowledge, by forcing a user calling max to supply this additional information.
-}
max' : (x : SeqDecProb)
    → (state : getstate x)
    → ((it : getstate x) → List (getcontrol x it)) -- 'it' for iterator.
    → (getcontrol x state → ℕ)
    → ℕ
max' x state controls f = foldl (λ n
                              → λ control → if n leq f control then f control else n)
                                 0
                                 allcontrols
  where
    allcontrols : List (getcontrol x state)
    allcontrols = controls state

{- Similar as for the max' function, this one requires a way to iterate over controls.
   This information is supplied by client code. Furthermore, a default control needs
   to be required in order to initiate the fold.
-}
argmax' : (x : SeqDecProb)
       → (state : getstate x)
       → ((it : getstate x) → List (getcontrol x it)) -- 'it' for iterator.
       → getcontrol x state                            -- default control
       → (getcontrol x state → ℕ)
       → getcontrol x state
argmax' x state controls defcont f = foldl (λ current → λ contender → if f current leq f contender then contender else current)
                                            defcont
                                            allcontrols
  where
    allcontrols : List (getcontrol x state)
    allcontrols = controls state

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

{- The new modified optimal extension needs two additional pieces of information. In
   order to properly propagate the control information to argmax, it needs to be
   supplied here. Furthermore, here we don't only need a default control, but a function
   that computes a default control for every state. This is because the control is a
   dependent type, but the state upon which it depends does not appear in the type, and
   thus it is not possible to get the control straight away.
-}
optExt' : {n : ℕ}
       → (x : SeqDecProb)
       → ((it : getstate x) → List (getcontrol x it))  -- proof of finiteness of the control space for every state
       → ((st : getstate x) → getcontrol x st)         -- always progress policy
       → PolicyPSeq x n
       → PolicyP x
optExt' x conts defaultcontrol ps state = argmax' x state conts (defaultcontrol state) f
  where f : getcontrol x state → ℕ
        f y = getreward x state y (getstep x state y) +
              val x (getstep x state y) ps

--OptExtLemma : {n : ℕ} → (x : SeqDecProb) → (ps : PolicyPSeq x n) → OptExt x ps (optExt x ps)
--OptExtLemma x ps p' state = {!!}

backwardsInduction : (n : ℕ) → (x : SeqDecProb) → PolicyPSeq x n
backwardsInduction zero x = []
backwardsInduction (suc n) x = (optExt x ps) ∷ ps
  where ps : PolicyPSeq x n
        ps = backwardsInduction n x

{- Finally, in order to properly propagate the information down to optExt' and
   argmax', even the backwardsinduction itself needs to accept these parameters
   as arguments.
-}
backwardsInduction2 : (n : ℕ)
                   → (x : SeqDecProb)
                   → ((it : getstate x) → List (getcontrol x it))
                   → ((st : getstate x) → getcontrol x st)
                   → PolicyPSeq x n
backwardsInduction2 zero x f defcont    = []
backwardsInduction2 (suc n) x f defcont = optExt' x f defcont ps ∷ ps
  where ps : PolicyPSeq x n
        ps = backwardsInduction2 n x f defcont

transitiveLTE : (x₁ x₂ x₃ : ℕ) → So (x₁ leq x₂) → So (x₂ leq x₃) → So (x₁ leq x₃)
transitiveLTE zero zero zero p₁ p₂ = oh
transitiveLTE zero zero (suc z) p₁ p₂ = oh
transitiveLTE zero (suc y) zero p₁ p₂ = oh
transitiveLTE zero (suc y) (suc z) p₁ p₂ = oh
transitiveLTE (suc x) zero zero () p₂
transitiveLTE (suc x) zero (suc z) () p₂
transitiveLTE (suc x) (suc y) zero p₁ ()
transitiveLTE (suc x) (suc y) (suc z) p₁ p₂ = transitiveLTE x y z p₁ p₂

{- Too lazy to do this now -}
postulate monotonePlus : (x y : ℕ) → (z : ℕ) → So (x leq y) → So ((z + x) leq (z + y))

Bellman : {n : ℕ}                →
          (x : SeqDecProb)       →
          (ps : PolicyPSeq x n)  →
          (OptPolicyPSeq x ps)   →
          (p : PolicyP x)        →
          OptExt x ps p          →
          OptPolicyPSeq x (p ∷ ps)
Bellman x ps ops p oep = opps
  where opps : OptPolicyPSeq x (p ∷ ps)
        opps state []          = oh
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
