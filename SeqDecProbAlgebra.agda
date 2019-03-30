module SeqDecProbAlgebra where

open import Data.Nat
open import Data.Bool hiding (_∨_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_; inj₁ to inl; inj₂ to inr)
open import Data.Maybe
open import Data.Unit
open import Data.Empty
open import Data.Vec

{- A dynamic system is a datatype of states together with a transition
   function. The transition function takes as input only the state, and
   from this computes a single new state. -}
record DynamicSystem : Set₁ where
  field
    State : Set
    Step  : State → State

{- A trajectory of a dynamic system is simply repeating the step function
   n times. -}
trajectoryDyn : (d : DynamicSystem) → DynamicSystem.State d → ((n : ℕ) → Vec (DynamicSystem.State d) n)
trajectoryDyn d x₀ = λ { zero    → [];
                         (suc n) → x₀ ∷ trajectoryDyn d (DynamicSystem.Step d x₀) n}

{- A sequential decision process (SDP) is a datatype of states, as in a dynamic
   system, but the step function now takes as an additional argument a
   control, which essentially represents an action that is possible in a
   state. Not all actions are possible in all states, and this behaviour is
   captured by the control. The control is dependent on the state. -}
record SeqDecProc : Set₁ where
  constructor SDP
  field
    State   : Set
    Control : State → Set
    Step    : (x : State) → (y : Control x) → State

{- A policy selects what control to use in a given state. It clearly must be
   dependent on a SeqDecProb, to know what type the state should be, i.e. -}
Policy : SeqDecProc → Set
Policy (SDP State Control Step) = (x : State) → Control x

{- A policy sequence is essentially just a vector of policies. -}
PolicySeq : SeqDecProc → ℕ → Set
PolicySeq s n = Vec (Policy s) n

{- A trajectory for a SDProc is computed in a similar way to that of a dynamic system.
   The main difference is that the step function now also accepts a control,
   which in each step is computed from the policy sequence.

   Given an initial state and a sequence of n policies, returns a vector of n
   states. -}
trajectorySDProc : (p : SeqDecProc) → (n : ℕ) → PolicySeq p n → (SeqDecProc.State p) → Vec (SeqDecProc.State p) n
trajectorySDProc p .0 [] x₀ = []
trajectorySDProc (SDP State Control Step) .(suc _) (x ∷ seq) x₀ = newstate ∷ trajectorySDProc (SDP State Control Step) _ seq newstate
  where newstate = Step x₀ (x x₀)

{- A SDP can be time dependent. This boils down to the idea of e.g that every
   control is not available at each point in time, thus adding a third
   dimension (time) to the problem. -}
record SeqDecProcTime : Set₁ where
  field
    State   : ℕ → Set
    Control : (n : ℕ) → State n → Set
    Step    : (n : ℕ) → (x : State n) → (y : Control n x) → State (suc n)
-- Note that it is now clear from the type that the step function moves forward in "time".

{- There is a trivial embedding of the non time dependent SDP in the time
   dependent case. The problem becomes one that takes time as a parameter
   to the fields, but does not care what value they are applied to. -}
embedTime : SeqDecProc → SeqDecProcTime
embedTime (SDP state control step)
                   = record {State   = λ time → state;
                             Control = λ time → control;
                             Step    = λ time → step}

{- Two individually defined SDPs can be combined as a product.

   The datatype of states becomes a product type, where each element contains the two
   prior states.

   The datatype capturing the controls would accept a state as argument,
   and apply the prior controls componentwise.

   The step function would accept a state and control as argument, and then apply
   the prior step functions componentwise.

   It is suitable to here take note that while the problems themselves are not dependent
   on each other, there is some dependency between them in the combined problem.
   Since both problems must be in a state at any given time, and they advance one step
   at the same time, if one of the problems reach a state where there are no controls
   available the other problem will not be able to advance either.
   Similarly, if one problem were to not have any states possible to begin with, the
   combined problem will never be able to advance. -}
productSDProc : SeqDecProc → SeqDecProc → SeqDecProc
productSDProc (SDP s₁ c₁ sf₁)
              (SDP s₂ c₂ sf₂)
                       = record {State   = s₁ × s₂;
                                 Control = λ state → c₁ (fst state) × c₂ (snd state);
                                 Step    = λ state → λ control → sf₁ (fst state) (fst control) , sf₂ (snd state) (snd control)}

{- If we would like a unit to combine with the product operation, it would be the unit process.
   Since the states of the prior processes will 'live' alongside eachother, and advance the
   problems using the step function at the same time, the process will have as states ⊤, the
   unit type. We can only construct one value of this type, tt. Similarly, there must only
   be one possible control, ⊤ & tt. The step function would take as input state tt, and as
   output always produce tt.

   p = a problem
   mul = productSDProc

   p `mul` productUnit =
   productUnit `mul` p =
   productUnit

Comment: Note that "=" is probably "isomorphic to" here.
 -}
productUnit : SeqDecProc
productUnit = record { State   = ⊤;
                       Control = λ state → ⊤;
                       Step    = λ state → λ control → tt}

{- Two problems can be combined as the sum of the problems. At any given time, the
   datatype representing the state will be either of the two prior states, and depending
   on which it will advance that state using its prior step function.

   Here we note that once the problem is in either of the states, it will never leave
   that process. It will advance the process using the prior state function, taking it
   to a new state belonging to the same prior process, and hence never leave the process.
   The processes are completely independent, as in contrast to the product case, even if
   one of the processes has no states to transition between the other process can still
   advance. -}
sumSDProc : SeqDecProc → SeqDecProc → SeqDecProc
sumSDProc (SDP s₁ c₁ sf₁)
          (SDP s₂ c₂ sf₂)
  = record { State   = s₁ ∨ s₂;
             Control = λ { (inl s₁) → (c₁ s₁);
                           (inr s₂) → (c₂ s₂)};
             Step    = (λ { (inl s₁) c → inl (sf₁ s₁ c);
                            (inr s₂) c → inr (sf₂ s₂ c) })}

{- If we want a unit problem to sumSDProc, we create a unit process based on the Empty
   datatype. A sum process can be in either of the two processes, and then stays there.
   Knowing this, if one of the processes has no states to ever be in the sum of the two
   processes could only ever be in the other process (given that it is not the unit, also).

   As state, we select the empty type. There is no way to construct states of this type.

   As control we also select the empty type. It is dependent on the state, but as the state
   is the empty type, and hence the initial type in the category of sets, we know that the
   function from the initial type to any other is unique, that this is the only function.

   As step function we need to go to a new state, given a prior state and a control. Once again,
   since now both state and control are initial types, again, the function we give is unique.

   Clearly, as we can not enter and evaluate such a process, the only 'viable' choice for the
   sum of both processes must be the other process.

   p = a problem
   plus = sumSDProc

   p `plus` sumUnit =
   sumUnit `plus` p =
   p -}
sumUnit : SeqDecProc
sumUnit = record {State   = ⊥;
                  Control = λ state → ⊥;
                  Step    = λ state → λ control → state}

swap-function : SeqDecProc → SeqDecProc → Set
swap-function p₁ p₂ = SeqDecProc.State p₁ → SeqDecProc.State p₂

{- An interesting extension of the sum process is one where during execution, the 'current'
   process would be able to yield in favor of the other process. We could capture this
   behaviour by giving the combinator two functions, one with domain s₁ and codomain s₂,
   and vice versa. The idea is that the available controls at any given point are captured
   in the Maybe monad. If there is a control, it is represented by a just control. If there
   is no available control, the 'value' of the control is nothing. If this is the case,
   the step function will instead call the given swap functions.

   An example situation could be if the processes modeled some software. One process could
   model some software that could potentially throw exceptions. The other process could
   model some error handler taking care of exceptions. The given 'swap'-functions would then
   be a map from 'exceptions' (states) to 'handlers' (states in the other process).
   The idea now is that if the software 'throws' an exception, there would be no available
   control/action to take. Instead the step function would look up the exception handler and
   switch to that process. When the handler-process reaches a state where the error has been
   taken care of, it would again have no controls/actions to take, but would instead yield
   in favor of the software again. -}
sumMaybeSDProc : (p₁ : SeqDecProc) → (p₂ : SeqDecProc) → swap-function p₁ p₂ → swap-function p₂ p₁ → SeqDecProc
sumMaybeSDProc (SDP s₁ c₁ sf₁)
               (SDP s₂ c₂ sf₂)
               swaps₁tos₂
               swaps₂tos₁
               = record { State   = s₁ ∨ s₂;
                          Control = λ { (inl s₁) → Maybe (c₁ s₁);
                                        (inr s₂) → Maybe (c₂ s₂)};
                          Step    = λ { (inl s₁) nothing → inr (swaps₁tos₂ s₁);
                                        (inl s₁) (just c₁) → inl (sf₁ s₁ c₁);
                                        (inr s₂) nothing → inl (swaps₂tos₁ s₂);
                                        (inr s₂) (just c₂) → inr (sf₂ s₂ c₂)}}

{- Two sequential decision processes can be interleaved, being allowed to advance
   one step every other time step. In the simplest case, with two processes, the 'toggle'
   can be thought of as a boolean. If it is true, advance one process, if it is false,
   advance the other. In reality, however, the toggle can be thought of as an index
   into the state, specifying which of the processes should advance. 

   This is not too different from the productSDProc, with some small details. In the
   product process, we had the 'problem' where if one process was 'empty' the other
   would not be able to progress. In the product process, if one process reached a point
   where it could not progress further, the entire process would sease to progress. In
   this interleaved process, we suffer a similar fate, with the exception that if the
   process that DO have available controls, it will be allowed to progress one step
   further.

   This situation could be similar to that of a game, where each player would take turns
   making their next move. However, the game would not be very interesting as the players
   do not possess the ability to inspect the other players moves. -}
interleaveSDProc : SeqDecProc → SeqDecProc → SeqDecProc
interleaveSDProc (SDP s₁ c₁ sf₁)
                 (SDP s₂ c₂ sf₂)
  = record { State   = Bool × (s₁ × s₂); -- index for product
             Control = λ { (false , x₁ , x₂) → c₁ x₁ ;
                           (true , x₁ , x₂)  → c₂ x₂};
             Step = λ { (false , x₁ , x₂) → λ control → true , sf₁ x₁ control , x₂ ;
                        (true , x₁ , x₂)  → λ control → false , x₁ , sf₂ x₂ control }}

{- Insted of a control depending on 'just' the state of a process, it could perhaps
   depend on the state of another process also. In the case of two interleaved problems,
   this captures e.g the notion of a game where the opponents last move is known. 

   This could perhaps be embodied in the Control field in the record somehow.. Since the
   interleaved process is built up of two existing ones i feel the need to actually use
   the original processes controls. -}
smart-control : SeqDecProc → SeqDecProc → Set
smart-control p₁ p₂ = (x₁ : SeqDecProc.State p₁)     →
                            SeqDecProc.State p₂      →
                            SeqDecProc.Control p₁ x₁ → SeqDecProc.Control p₁ x₁

{- Using this smart control, which bases a processes next move based on the original processes
   control as well as the other processes current state. Now imagine a game of chess
   where your next move is based not only on the state of your pieces on the board,
   but also your opponents pieces. -}
interleaveSDProcClever : (p₁ : SeqDecProc) → (p₂ : SeqDecProc) → smart-control p₁ p₂ → smart-control p₂ p₁ → SeqDecProc
interleaveSDProcClever (SDP s₁ c₁ sf₁) (SDP s₂ c₂ sf₂) sc₁ sc₂
  = record {State   = Bool × s₁ × s₂;
            Control = λ { (true , x₁ , x₂)  → c₁ x₁;
                          (false , x₁ , x₂) → c₂ x₂};
            Step    = λ { (true , x₁ , x₂) → λ control → false , sf₁ x₁ (sc₁ x₁ x₂ control) , x₂ ;
                          (false , x₁ , x₂)  → λ control → true , x₁ , sf₂ x₂ (sc₂ x₂ x₁ control) }}





record SeqDecProb (A : Set) : Set₂ where
  field
    State : Set
    Control : State -> Set

    step : (x : State) -> (y : Control x) -> State

    val : Set  -- with 0, (+), (<=). Perhaps as parameter to the rec. type.
    reward : (x : State) -> (y : Control x) -> (x' : State) -> A

{-

Project idea: implement an algebra (a category?) of SeqDecProbs and
  explore their properties.

  unit, product, sum, etc.

Student: Robert Krook, UGOT, CS 5:th year.

-}
