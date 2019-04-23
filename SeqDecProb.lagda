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
    State : Set
    Control : State -> Set

    Step : (x : State) -> (y : Control x) -> State

    Val : Set  -- with 0, (+), (<=). perhaps as parameter to the rec. type.
    Reward : (x : State) -> (y : Control x) -> (x' : State) -> ℕ -- should be Val

getstate   = SeqDecProb.State
getcontrol = SeqDecProb.Control
getstep    = SeqDecProb.Step
getreward  = SeqDecProb.Reward

productSDProb : SeqDecProb → SeqDecProb → SeqDecProb
productSDProb (SDProb s₁ c₁ sf₁ Val r₁)
              (SDProb s₂ c₂ sf₂ Val₁ r₂) =
              SDProb
                (s₁ × s₂)
                (λ state → c₁ (proj₁ state) × c₂ (proj₂ state))
                (λ state → λ control → sf₁ (proj₁ state) (proj₁ control) , sf₂ (proj₂ state) (proj₂ control))
                Val
                λ state → λ control → λ next → r₁ (proj₁ state) (proj₁ control) (proj₁ next) + r₂ (proj₂ state) (proj₂ control) (proj₂ next)

Policy : SeqDecProb → Set
Policy (SDProb State Control Step Val Reward) = (x : State) → Control x

PolicySeq : SeqDecProb → ℕ → Set
PolicySeq x n = Vec (Policy x) n

trajectory : (x : SeqDecProb) → {n : ℕ} → getstate x → PolicySeq x n → Vec (getstate x) n
trajectory x x₀ [] = []
trajectory x x₀ (y ∷ seq) = x₀ ∷ trajectory x x' seq
  where x' : getstate x
        x' = getstep x x₀ (y x₀)
\end{code}
