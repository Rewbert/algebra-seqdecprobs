module ExampleDynamicSystem where

open import Data.Nat
open import Data.Vec

open import SeqDecProbAlgebra

data State : Set where
  One   : State
  Two   : State
  Three : State
  Four  : State

transition : State → State
transition One = Two
transition Two = Three
transition Three = Four
transition Four = One

sys : DynamicSystem
sys = record { State = State; Step = transition}

example : (n : ℕ) → Vec State n
example n = trajectoryDyn sys One n
