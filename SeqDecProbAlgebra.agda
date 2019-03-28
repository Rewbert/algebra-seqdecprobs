module SeqDecProbAlgebra where

open import Data.Nat
open import Data.Bool hiding (_∨_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_; inj₁ to inl; inj₂ to inr)
open import Data.Maybe
open import Data.Unit
open import Data.Empty

{- A dynamic system is a datatype of states together with a transition 
   function. The transition function takes as input only the state, and 
   from this computes a single new state. -}
record DynamicSystem : Set₁ where
  field
    State : Set
    Step  : State → State

{- A sequential decision process (SDP) is a datatype of states, as in a dynamic
   system, but the step function now takes as an additional argument a
   control, which essentially represents an action that is possible in a
   state. Not all actions are possible in all states, and this behaviour is
   captured by the control. The control is dependent on the state. -}
record SeqDecProc : Set₁ where
  field
    State   : Set
    Control : State → Set
    Step    : (x : State) → (y : Control x) → State

{- A SDP can be time dependent. This boils down to the idea of e.g that every 
   control is not available at each point in time, thus adding a third 
   dimension (time) to the problem. -}
record SeqDecProcTime : Set₁ where
  field
    State   : ℕ → Set
    Control : (n : ℕ) → State n → Set
    Step    : (n : ℕ) → (x : State n) → (y : Control n x) → State (suc n)

{- There is a trivial embedding of the non time dependent SDP in the time
   dependent case. The problem becomes one that takes time as a parameter
   to the fields, but does not care what value they are applied to. -}
embedTime : SeqDecProc → SeqDecProcTime
embedTime record { State   = state ;
                   Control = control ;
                   Step    = step }
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
productSDProc record { State   = s₁ ;
                       Control = c₁ ;
                       Step    = sf₁ }
              record { State   = s₂ ;
                       Control = c₂ ;
                       Step    = sf₂ }
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
   productUnit -}
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
sumSDProc record { State   = s₁ ;
                   Control = c₁ ;
                   Step    = sf₁ }
          record { State   = s₂ ;
                   Control = c₂ ;
                   Step    = sf₂ } = record { State   = s₁ ∨ s₂;
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
sumMaybeSDProc : (p₁ : SeqDecProc) → (p₂ : SeqDecProc) → (SeqDecProc.State p₁ → SeqDecProc.State p₂) →
                                                           (SeqDecProc.State p₂ → SeqDecProc.State p₁) → SeqDecProc
sumMaybeSDProc record { State   = s₁ ;
                        Control = c₁ ;
                        Step    = sf₁ }
               record { State   = s₂ ;
                        Control = c₂ ;
                        Step    = sf₂ }
               swaps₁tos₂
               swaps₂tos₁
               = record { State   = s₁ ∨ s₂;
                          Control = λ { (inl s₁) → Maybe (c₁ s₁);
                                        (inr s₂) → Maybe (c₂ s₂)};
                          Step    = λ { (inl s₁) nothing → inr (swaps₁tos₂ s₁);
                                        (inl s₁) (just c₁) → inl (sf₁ s₁ c₁);
                                        (inr s₂) nothing → inl (swaps₂tos₁ s₂);
                                        (inr s₂) (just c₂) → inr (sf₂ s₂ c₂)}}

interleaveSDProc : SeqDecProc → SeqDecProc → SeqDecProc
interleaveSDProc record { State   = s₁ ;
                          Control = c₁ ;
                          Step    = sf₁ }
                 record { State   = s₂ ;
                          Control = c₂ ;
                          Step    = sf₂ }
                          = record { State   = Bool × (s₁ × s₂); -- index for product
                                     Control = λ state → c₁ (fst (snd state)) × c₂ (snd (snd state));
                                     Step    = λ state → λ control → if fst state
                                                                     then false , (sf₁ (fst (snd state)) (fst control) , snd (snd state))
                                                                     else (true , (fst (snd state) , sf₂ (snd (snd state)) (snd control)))}












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
