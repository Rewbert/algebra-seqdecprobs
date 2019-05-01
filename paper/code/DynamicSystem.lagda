% -*- latex -*-
\begin{code}[hide]
module DynamicSystem where

record DynamicSystem : Set₁ where
  field
    State : Set
    step  : State → State
\end{code}
