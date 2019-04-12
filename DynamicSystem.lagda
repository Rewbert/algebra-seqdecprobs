\begin{code}
open import Data.Nat
open import Data.Vec
\end{code}

{- A dynamic system is a datatype of states together with a transition
   function. The transition function takes as input only the state, and
   from this computes a single new state. -}
\begin{code}
record DynamicSystem : Set₁ where
  field
    State : Set
    Step  : State → State

{- A trajectory of a dynamic system is simply repeating the step function
   n times. -}
trajectoryDyn : (d : DynamicSystem) → DynamicSystem.State d → (n : ℕ) → Vec (DynamicSystem.State d) n
trajectoryDyn d x₀ zero = []
trajectoryDyn d x₀ (suc n) = x₀ ∷ trajectoryDyn d x₁ n
  where x₁ : DynamicSystem.State d
        x₁ = DynamicSystem.Step d x₀

getdstate : DynamicSystem → Set
getdstate system = DynamicSystem.State system
\end{code}
