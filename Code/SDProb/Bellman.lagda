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
import VSDProb

data So : Bool → Set where
  oh : So true

_<=_ : ℕ → ℕ → Bool
zero   <=  n       =  true
suc m  <=  zero    =  false
suc m  <=  suc n   =  m <= n

-- TODO make sys a parameter, not an index
data CtrlSeq : (sys : SeqDecProb) → # sys → ℕ → Set where
    nil : (sys : SeqDecProb) → (state : # sys) → CtrlSeq sys state zero
    _∷_ : {n : ℕ} → (sys : SeqDecProb) →
           (state : # sys)            →
           (y : getcontrol sys state)        →
           CtrlSeq sys (getstep sys state y) n →
           CtrlSeq sys state (suc n)

value : {n : ℕ} → (sys : SeqDecProb) → (state : # sys) → CtrlSeq sys state n → ℕ
value sys state (nil .sys .state) = 0
value sys state ((.sys ∷ .state) y seq) =
  getreward sys state y (getstep sys state y) +
  value sys (getstep sys state y) seq

OptCtrlSeq : {n : ℕ} → (sys : SeqDecProb) → (state : # sys) → CtrlSeq sys state n → Set
OptCtrlSeq sys state seq =
  {n : ℕ} → (ys : CtrlSeq sys state n) → So (value sys state ys <= value sys state seq)

PolicyP : SeqDecProb →  Set
PolicyP (SDProb state control step reward) = (x : state) → control x

PolicyPSeq : SeqDecProb → ℕ → Set
PolicyPSeq sys n = Vec (PolicyP sys) n

val : {n : ℕ} → (sys : SeqDecProb) → (state : # sys) → PolicyPSeq sys n → ℕ
val sys state [] = 0
val sys state (p ∷ seq) = getreward sys state (p state) x' + val sys x' seq
  where x' : # sys
        x' = getstep sys state (p state)

OptPolicyPSeq : {n : ℕ} → (sys : SeqDecProb) → PolicyPSeq sys n → Set
OptPolicyPSeq sys seq = {n : ℕ}                →
                      (state : # sys)   →
                      (ps' : PolicyPSeq sys n) →
                      So (val sys state ps' <= val sys state seq)

OptExt : {n : ℕ} → (sys : SeqDecProb) → PolicyPSeq sys n → PolicyP sys → Set
OptExt sys seq p = (p' : PolicyP sys)     →
                   (state : # sys) →
                   So (val sys state (p' ∷ seq) <= val sys state (p ∷ seq))

{- Given a state and a function which from controls available in that state computes
   a value (reward), returns the maximum of therese rewards obtainable.
   How to 'terate' over all possible controls? -}
max : (sys : SeqDecProb) → (state : # sys) → (getcontrol sys state → ℕ) → ℕ
max sys state f = {!!}

{- In order to implement max we need to specify an additional piece of information, namely
   how to iterate over all possible controls for a given state. An assumption is made
   about having this knowledge, by forcing a user calling max to supply this additional information.
-}
max' : (sys : SeqDecProb)
    → (state : # sys)
    → ((it : # sys) → List (getcontrol sys it)) -- 'it' for iterator.
    → (getcontrol sys state → ℕ)
    → ℕ
max' sys state controls f = foldl (λ n
                              → λ control → if n <= f control then f control else n)
                                 0
                                 allcontrols
  where
    allcontrols : List (getcontrol sys state)
    allcontrols = controls state

{- Similar as for the max' function, this one requires a way to iterate over controls.
   This information is supplied by client code. Furthermore, a default control needs
   to be required in order to initiate the fold.
-}
argmax' : (sys : SeqDecProb)
       → (state : # sys)
       → ((it : # sys) → List (getcontrol sys it)) -- 'it' for iterator.
       → getcontrol sys state                            -- default control
       → (getcontrol sys state → ℕ)
       → getcontrol sys state
argmax' sys state controls defcont f = foldl (λ current → λ contender → if f current <= f contender then contender else current)
                                            defcont
                                            allcontrols
  where
    allcontrols : List (getcontrol sys state)
    allcontrols = controls state

{- Similarly to max, computes based on the same principle, but returns the argument (control)
   that produced this maximum reward. -}
argmax : (sys : SeqDecProb) → (state : # sys) → (getcontrol sys state → ℕ) → getcontrol sys state
argmax sys state f = {!!}

MaxSpec : Set₁
MaxSpec = (sys : SeqDecProb) → (state : # sys) → (f : getcontrol sys state → ℕ) →
          (y : getcontrol sys state) → So (f y <= max sys state f)

ArgmaxSpec : Set₁
ArgmaxSpec = (sys : SeqDecProb) → (state : # sys) → (f : getcontrol sys state → ℕ) → So (f (argmax sys state f) == max sys state f)

optExt : {n : ℕ} → (sys : SeqDecProb) → PolicyPSeq sys n → PolicyP sys
optExt sys ps state = argmax sys state f
  where f : getcontrol sys state → ℕ
        f y = getreward sys state y (getstep sys state y) +
              val sys (getstep sys state y) ps

{- The new modified optimal extension needs two additional pieces of information. In
   order to properly propagate the control information to argmax, it needs to be
   supplied here. Furthermore, here we don't only need a default control, but a function
   that computes a default control for every state. This is because the control is a
   dependent type, but the state upon which it depends does not appear in the type, and
   thus it is not possible to get the control straight away.
-}
optExt' : {n : ℕ}
       → (sys : SeqDecProb)
       → ((it : # sys) → List (getcontrol sys it))  -- proof of finiteness of the control space for every state
       → ((st : # sys) → getcontrol sys st)         -- always progress policy
       → PolicyPSeq sys n
       → PolicyP sys
optExt' sys conts defaultcontrol ps state = argmax' sys state conts (defaultcontrol state) f
  where f : getcontrol sys state → ℕ
        f y = getreward sys state y (getstep sys state y) +
              val sys (getstep sys state y) ps

--OptExtLemma : {n : ℕ} → (sys : SeqDecProb) → (ps : PolicyPSeq sys n) → OptExt sys ps (optExt sys ps)
--OptExtLemma sys ps p' state = {!!}

backwardsInduction : (n : ℕ) → (sys : SeqDecProb) → PolicyPSeq sys n
backwardsInduction zero sys = []
backwardsInduction (suc n) sys = (optExt sys ps) ∷ ps
  where ps : PolicyPSeq sys n
        ps = backwardsInduction n sys

{- Finally, in order to properly propagate the information down to optExt' and
   argmax', even the backwardsinduction itself needs to accept these parameters
   as arguments.
-}
backwardsInduction2 : (n : ℕ)
                   → (sys : SeqDecProb)
                   → ((it : # sys) → List (getcontrol sys it))
                   → ((st : # sys) → getcontrol sys st)
                   → PolicyPSeq sys n
backwardsInduction2 zero sys f defcont    = []
backwardsInduction2 (suc n) sys f defcont = optExt' sys f defcont ps ∷ ps
  where ps : PolicyPSeq sys n
        ps = backwardsInduction2 n sys f defcont

transitiveLTE : (x₁ x₂ x₃ : ℕ) → So (x₁ <= x₂) → So (x₂ <= x₃) → So (x₁ <= x₃)
transitiveLTE zero zero zero p₁ p₂ = oh
transitiveLTE zero zero (suc z) p₁ p₂ = oh
transitiveLTE zero (suc y) zero p₁ p₂ = oh
transitiveLTE zero (suc y) (suc z) p₁ p₂ = oh
transitiveLTE (suc x) zero zero () p₂
transitiveLTE (suc x) zero (suc z) () p₂
transitiveLTE (suc x) (suc y) zero p₁ ()
transitiveLTE (suc x) (suc y) (suc z) p₁ p₂ = transitiveLTE x y z p₁ p₂

{- Too lazy to do this now -}
postulate monotonePlus : (x y : ℕ) → (z : ℕ) → So (x <= y) → So ((z + x) <= (z + y))

Bellman : {n : ℕ}                →
          (sys : SeqDecProb)       →
          (ps : PolicyPSeq sys n)  →
          (OptPolicyPSeq sys ps)   →
          (p : PolicyP sys)        →
          OptExt sys ps p          →
          OptPolicyPSeq sys (p ∷ ps)
Bellman sys ps ops p oep = opps
  where opps : OptPolicyPSeq sys (p ∷ ps)
        opps state []          = oh
        opps state (p' ∷ ps') = transitiveLTE (val sys state (p' ∷ ps'))
                                               (val sys state (p' ∷ ps))
                                               (val sys state (p ∷ ps))
                                               step2
                                               step3
          where step1 : So (val sys (getstep sys state (p' state)) ps' <= val sys (getstep sys state (p' state)) ps)
                step1 = ops (getstep sys state (p' state)) ps'
                step2 : So (val sys state (p' ∷ ps') <= val sys state (p' ∷ ps))
                step2 = monotonePlus (val sys (getstep sys state (p' state)) ps')
                                     (val sys (getstep sys state (p' state)) ps)
                                     (getreward sys state (p' state)
                                     (getstep sys state (p' state))) step1
                step3 : So (val sys state (p' ∷ ps) <= val sys state (p ∷ ps))
                step3 = oep p' state

\end{code}
