\begin{code}
open import Data.Nat
open import Data.Bool
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
\end{code}
