\begin{code}
module ExampleSeqDecProb where

open import Data.Nat hiding (_<_)
open import Agda.Builtin.Nat
open import Data.Product hiding (map)
open import Function
open import Data.Vec hiding (_++_)
open import Data.List hiding (zipWith) renaming (map to listmap)
open import Data.Unit
open import Data.Bool


--open import SeqDecProb

--open import SeqDecProc
open import SeqDecProb renaming (Policy to PolicyP; PolicySeq to PolicyPSeq)
open import Bellman using (val; backwardsInduction2)

{- One dimensional state -}
1d-state : Set
1d-state = ℕ

{- If the state is 0 we have two possible controls, stay or right-}
data ZAction : Set where
  ZS : ZAction -- stay for zero state
  ZR : ZAction -- right for zero state

{- Otherwise, the controlspace contains three controls. Left, stay and right. -}
data SAction : Set where
  SL : SAction -- left
  SS : SAction -- stay
  SR : SAction -- right

{- One dimensional control, depends on state -}
1d-control : 1d-state → Set
1d-control zero    = ZAction
1d-control (suc s) = SAction

1d-step : (x : 1d-state) → 1d-control x → 1d-state
1d-step zero ZR = 1
1d-step zero ZS = zero
1d-step (suc x) SL = x
1d-step (suc x) SS = suc x
1d-step (suc x) SR = suc (suc x)

\end{code}
1d-system : SeqDecProc
1d-system = SDP 1d-state 1d-control 1d-step

left : Policy 1d-system   -- tryleft (may not succeed to actuall move left)
left zero = ZS
left (suc n) = SL

right : Policy 1d-system
right zero  = ZR
right (suc n) = SR

stay : Policy 1d-system
stay zero = ZS
stay (suc n) = SS

1d-example : Vec 1d-state 5
1d-example = trajectorySDProc 1d-system
               (right ∷ right ∷ stay ∷ left ∷ left ∷ []) 0
\begin{code}
distance : ℕ → ℕ → ℕ    -- distance m n = abs (m-n)  informally
distance zero zero       = 0
distance zero (suc m)    = 1 + distance zero m
distance (suc n) zero    = 1 + distance n zero
distance (suc n) (suc m) = distance n m

large = 100

-- Parameterised reward function used to "steer" towards a desired goal position
--    (x : State) -> (y : Control x) -> (x' : State) -> ℕ
1d-reward : (goal : 1d-state) →      (x : 1d-state) → 1d-control x -> 1d-state -> ℕ
1d-reward goal x y next = large ∸ distance goal next


1d-prob-system : ℕ → SeqDecProb
1d-prob-system n = SDProb 1d-state 1d-control 1d-step ℕ (1d-reward n)

2d-problem : (goal₁ goal₂ : ℕ) → SeqDecProb
2d-problem goal₁ goal₂ = productSDProb (1d-prob-system goal₁) (1d-prob-system goal₂)

getcontrols : (state : 1d-state) → List (1d-control state)
getcontrols zero         = ZS ∷ ZR ∷ []
getcontrols (suc state₁) = SL ∷ SS ∷ SR ∷ []

defaultcontrols : (state : 1d-state) → 1d-control state
defaultcontrols zero         = ZS
defaultcontrols (suc state₁) = SS

testrun : (n goal : ℕ) → Vec 1d-state n
testrun n goal = trajectory (1d-prob-system goal) 10 (backwardsInduction2 n (1d-prob-system goal) getcontrols defaultcontrols)

cart : {A B : Set} → List A → List B → List (A × B)
cart [] l₂ = []
cart (a ∷ l₁) l₂ = listmap (λ b → a , b) l₂ ++ cart l₁ l₂

2d-getcontrols : (goal₁ goal₂ : ℕ) → (state : getstate (2d-problem goal₁ goal₂)) → List (getcontrol (2d-problem goal₁ goal₂) state)
2d-getcontrols goal₁ goal₂ (l , r) = cart (getcontrols l) (getcontrols r)

2d-defaultcontrols : (goal₁ goal₂ : ℕ) → (state : getstate (2d-problem goal₁ goal₂)) → getcontrol (2d-problem goal₁ goal₂) state
2d-defaultcontrols goal₁ goal₂ (l , r) = defaultcontrols l , defaultcontrols r

test2drun : (n goal₁ goal₂ : ℕ) → Vec (getstate (2d-problem goal₁ goal₂)) n
test2drun n goal₁ goal₂ = trajectory
                            (2d-problem goal₁ goal₂)
                            (0 , 0)
                            (backwardsInduction2
                              n
                              (2d-problem goal₁ goal₂)
                              (2d-getcontrols goal₁ goal₂)
                              (2d-defaultcontrols goal₁ goal₂))
\end{code}
