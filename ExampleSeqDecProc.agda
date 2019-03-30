module ExampleSeqDecProc where

open import Data.Nat
open import Data.Product hiding (map)
open import Function
open import Data.Vec

open import SeqDecProbAlgebra

{- An example state could be a set of coordinates -}
state : Set
state = ℕ × ℕ

{- A control could tell us which direction we could go at (excluding diagonal steps). -}
data Control : state → Set where
  Left     : (x : state) → Control x
  Forward  : (x : state) → Control x
  Backward : (x : state) → Control x
  Right    : (x : state) → Control x

{- A step function will advance the proper coordinate to its next state. -}
step : (x : state) → Control x → state
step (x , y) (Left     .(x , y)) = x ∸ 1 , y
step (x , y) (Forward  .(x , y)) = x , y + 1
step (x , y) (Backward .(x , y)) = x , y ∸ 1
step (x , y) (Right    .(x , y)) = x + 1 , y

{- These three components are enough to already define a sequential decision process. -}
system : SeqDecProc
system = SDP state Control step

{- In the case of this system, the Controls are not very interesting as they don't really
   look inside x. In a more interesting case, perhaps a Control could whitelist possible moves,
   and the policy would pick either of them. The way ∸ works we are not in any trouble, but
   maybe the policy could stop us from going out of bounds.  -}
leftPolicy : Policy system
leftPolicy x = Left x

rightPolicy : Policy system
rightPolicy x = Right x

forwardPolicy : Policy system
forwardPolicy x = Forward x

backwardPolicy : Policy system
backwardPolicy x = Backward x

{- An example policy sequence. -}
policyseq : PolicySeq system 5
policyseq = forwardPolicy ∷ backwardPolicy ∷ leftPolicy ∷ rightPolicy ∷ rightPolicy ∷ [] 

{- If we run this system, using the above defined policy sequence with a starting state of
   position (5, 5), it will look like this. The end result should be (6, 5). -}
example : Vec state 5
example = trajectorySDProc system 5 policyseq (5 , 5)

{- As an example, we could combine the product system. -}
newsystem : SeqDecProc
newsystem = productSDProc system system

{- We can reuse a lot, but we can not reuse the policy sequence used for the singular problem.
   This is where the backwards induction would be handy. Just as an example, i am here converting
   the original policy sequence to one that applices the policy componentwise. -}
newsystemexample : Vec (SeqDecProc.State newsystem) 5
newsystemexample = trajectorySDProc
                     newsystem
                     5
                     (map (λ prior-policy →
                           λ new-state    →
                           prior-policy (proj₁ new-state) , prior-policy (proj₂ new-state))
                           policyseq)
                     ((0 , 0) , 10 , 10)

{- To realise the statements made in SeqDecProbAlgebra.agda about not being able to advance
   the product of two processes if one of the processes is the initial process, we compute
   if here using the identity for sumSDProc. -}
cantprogress : SeqDecProc
cantprogress = productSDProc system sumUnit

{- We can never advance the cantprogress process. We can not give an initial state. -}
cantprogressexample : Vec (SeqDecProc.State cantprogress) 5
cantprogressexample = trajectorySDProc
                        cantprogress
                        5
                        (map (λ prior-policy →
                             λ new-state     →
                             {- we can 'cheat' and create a policy for the new problem.
                                The policy takes as argument an element of the new process, whose
                                second component happen to be of the same type as the control. We
                                can simply project this component and get something the typechecker
                                likes. However, we will never be able to create such a value and call
                                this function.

                                Please note though, that the choice of ⊥ as type of Control need not be
                                the case. It should be enough that either the state or control is of type
                                ⊥ to make sure the system can never be advanced. -}
                             prior-policy (proj₁ new-state) , proj₂ new-state)
                             policyseq)
                        ((5 , 5) , {!can not create a value of ⊥, implementation stops here!})
