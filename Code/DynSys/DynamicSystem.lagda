\begin{code}
open import Data.Nat
open import Data.Vec
\end{code}

A dynamic system is a datatype of states together with a transition
function. The transition function takes as input only the state, and
from this computes a single new state.

\begin{code}
record DynamicSystem : Set₁ where
  field
    State : Set
    step  : State → State

-- shorter accessor name
getdstate : DynamicSystem → Set
getdstate = DynamicSystem.State

-- even shorter
# = getdstate


{- A trajectory of a dynamic system is simply repeating the step function
   n times. -}
trajectoryDyn : (d : DynamicSystem) → # d → (n : ℕ) → Vec (# d) n
trajectoryDyn d x₀ zero = []
trajectoryDyn d x₀ (suc n) = x₀ ∷ trajectoryDyn d x₁ n
  where x₁ : # d
        x₁ = DynamicSystem.step d x₀
\end{code}
