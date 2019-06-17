\begin{code}
module core.dfa where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Bool
open import Data.Vec
open import Relation.Binary.PropositionalEquality
\end{code}

Main differences:
  - control space (alphabet) is constant. 'Bad' controls
    lead to dead state, while they are excluded completely
    in SDProc.
  - in a SDProc it is completely arbitrary where a process
    begins and stops evaluation.
  - it seems like a dfa can be turned into a sdproc by forgetting
    the properties of initial and final states. They are two very
    different things however, with very different properties.

\begin{code}
record DeterministicFiniteAutomata : Set₁ where
  constructor DFA
  field
    -- | A set of states
    Q  : Set

    -- | An alphabet
    Σ  : Set

    -- | An initial state
    x₀ : Q

    -- | A transition function
    δ  : Σ → Q → Q

    -- | A set of final states (should be a subset of Q to be as correct as possible)
    F  : List Q

    -- | Need some way of comparing elements, not part of DFA description, but needed here.
    eq : Q → Q → Bool

  -- | Is a state a final state?  Just iterates through the
  -- | list of final states and checks if any is equal.
  isaccepted : Q → Bool
  isaccepted x = isaccepted' x F
    where isaccepted' : Q → List Q → Bool
          isaccepted' x [] = false
          isaccepted' x (head ∷ word) = if   eq x head
                                         then true
                                         else isaccepted' x word

  -- | Evaluating a DFA on an input boils down to a reduction
  -- | on the transition function, consuming one symbol at a time.
  run' : Q → List Σ → Bool
  run' s []             = isaccepted s
  run' s (head ∷ word) = run' (δ head s) word

  eval : List Σ → Bool
  eval word = run' x₀ word

--------------- | Example | --------------

data State : Set where
  S1   : State
  S2   : State
  S3   : State
  Dead : State

eq' : State → State → Bool
eq' S1 S1     = true
eq' S1 l      = false
eq' S2 S2     = true
eq' S2 l      = false
eq' S3 S3     = true
eq' S3 l      = false
eq' Dead Dead = true
eq' Dead l    = false

data Σ' : Set where
  a : Σ'
  b : Σ'

δ' : Σ' → State → State
δ' a S1   = S1
δ' b S1   = S2
δ' a S2   = S3
δ' b S2   = S1
δ' a S3   = S3
δ' b S3   = Dead
δ' l Dead = Dead

dfa' = DFA State Σ' S1 δ' (S3 ∷ []) eq'

#eval = DeterministicFiniteAutomata.eval

goodword1 : #eval dfa' (a ∷ b ∷ a ∷ a ∷ []) ≡ true
goodword1 = refl

goodword2 : #eval dfa' (b ∷ a ∷ []) ≡ true
goodword2 = refl

badword : #eval dfa' (a ∷ []) ≡ false
badword = refl

open import core.seqdecproc

-- | Forgetful embedding, forgets where the automata 'starts' and where it ends.
DFA→SDP : DeterministicFiniteAutomata → SDProc
DFA→SDP (DFA Q Σ x₀ δ F eq) =
    SDP Q
        (λ _ → Σ)
        (λ state → λ symbol → δ symbol state)

-- | Can not implement this.
SDP→DFA : SDProc → DeterministicFiniteAutomata
SDP→DFA (SDP S C sf) =
    DFA S
        {!!} -- have no (s : S) to apply to C to get the control space
        {!!} -- what state is initial?
        (λ symbol → λ state → sf state {!!})
        {!!} -- where does it end?
        {!!} -- how to compare? Can only give trivial definitions (const true or const false)
\end{code}
