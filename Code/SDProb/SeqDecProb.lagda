\begin{code}
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Vec

\end{code}

\begin{code}
record SeqDecProb : Set₁ where
  constructor SDProb
  field
    State    : Set
    Control  : State -> Set

    step     : (x : State) -> (y : Control x) -> State

--    Val     : Set  -- with |0|, |(+)|, |(<=)|. Perhaps as parameter to the rec. type. (product requres the same Val)
    reward  : (x : State) -> (y : Control x) -> (x' : State) -> ℕ -- should be |Val|

getstate   = SeqDecProb.State
getcontrol = SeqDecProb.Control
getstep    = SeqDecProb.step
getreward  = SeqDecProb.reward

# = getstate

productSDProb : SeqDecProb → SeqDecProb → SeqDecProb
productSDProb (SDProb S₁ C₁ sf₁ r₁)
              (SDProb S₂ C₂ sf₂ r₂) =
              SDProb
                (S₁ × S₂)
                (λ state → C₁ (proj₁ state) × C₂ (proj₂ state))
                (λ state → λ control → sf₁ (proj₁ state) (proj₁ control) , sf₂ (proj₂ state) (proj₂ control))
                λ state → λ control → λ next → r₁ (proj₁ state) (proj₁ control) (proj₁ next) + r₂ (proj₂ state) (proj₂ control) (proj₂ next)

Policy : SeqDecProb → Set
Policy (SDProb State Control _ _) = (x : State) → Control x

PolicySeq : SeqDecProb → ℕ → Set
PolicySeq x n = Vec (Policy x) n

trajectory : (sys : SeqDecProb) → {n : ℕ} → # sys → PolicySeq sys n → Vec (# sys) n
trajectory sys x [] = []
trajectory sys x (p ∷ ps) = x ∷ trajectory sys next ps
  where next : # sys
        next = getstep sys x (p x)
\end{code}
