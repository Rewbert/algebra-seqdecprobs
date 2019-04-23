module ExampleSeqDecProc where

open import Data.Nat hiding (_<_)
open import Agda.Builtin.Nat
open import Data.Product hiding (map)
open import Function
open import Data.Vec hiding (_++_)
open import Data.List hiding (zipWith) renaming (map to listmap)
open import Data.Unit
open import Data.Bool


open import SeqDecProbAlgebra

open import SeqDecProc
open import SeqDecProb renaming (Policy to PolicyP; PolicySeq to PolicyPSeq)
open import Bellman using (val; backwardsInduction2)

{- An example state could be a set of coordinates -}
state : Set
state = ℕ × ℕ

{- A control could tell us which direction we could go at (excluding diagonal steps). -}
data Control : state → Set where
  Left     : (x : state) → Control x
  Forward  : (x : state) → Control x
  Backward : (x : state) → Control x
  Right    : (x : state) → Control x

-- try to make a 1-D version, then cross it with itself and compare with this 2-D version
-- make a version which disallows "bad" moves instead of using "monus"

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
policyseq = forwardPolicy ∷ leftPolicy ∷ backwardPolicy ∷ rightPolicy ∷ forwardPolicy ∷ []

{- If we run this system, using the above defined policy sequence with a starting state of
   position (5, 5), it will look like this. The end result should be (6, 5). -}
example : Vec state 5
example = trajectorySDProc system policyseq (5 , 5)

{- As an example, we could combine the product system. -}
newsystem : SeqDecProc
newsystem = productSDProc system system

{- We can reuse a lot, but we can not reuse the policy sequence used for the singular problem.
   This is where the backwards induction would be handy. Just as an example, i am here converting
   the original policy sequence to one that applices the policy componentwise. -}
newsystemexample : Vec (SeqDecProc.State newsystem) 5
newsystemexample = trajectorySDProc
                     newsystem
                     (map (λ prior-policy →
                           λ new-state    →
                           prior-policy (proj₁ new-state) , prior-policy (proj₂ new-state))
                           policyseq)
                     ((0 , 0) , 10 , 10)

bar : {n : ℕ} -> PolicySeq system n -> PolicySeq newsystem n
bar = map (λ prior-policy →
           λ new-state    →
           prior-policy (proj₁ new-state) , prior-policy (proj₂ new-state))

prodPolicy : {n : ℕ} -> PolicySeq system n -> PolicySeq system n -> PolicySeq newsystem n
prodPolicy = zipWith (λ p-p-1 → λ p-p-2 → λ new-state    →
                      p-p-1 (proj₁ new-state) , p-p-2 (proj₂ new-state))

foo : PolicySeq newsystem 5
foo = prodPolicy policyseq policyseq

-- TODO clean up combinator for product of policy sequences

{- To realise the statements made in SeqDecProbAlgebra.agda about not being able to advance
   the product of two processes if one of the processes is the initial process, we compute
   if here using the identity for sumSDProc. -}
cantprogress : SeqDecProc
cantprogress = productSDProc system sumUnit

{- We can never advance the cantprogress process. We can not give an initial state. -}
cantprogressexample : Vec (SeqDecProc.State cantprogress) 5
cantprogressexample = trajectorySDProc
                        cantprogress
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

{- One dimensional state -}
1d-state : Set
1d-state = ℕ

{- If the state is 0 we have two possible controls, stay or right-}
data ZAction : Set where
  ZS : ZAction -- stay for zero state
  ZR : ZAction -- right for zero state

{- Otherwise, the controlspace contains three controls. Left, stay and right. -}
data SAction : Set where
  SL : SAction -- left
  SS : SAction -- stay
  SR : SAction -- right

{- One dimensional control, depends on state -}
1d-control : 1d-state → Set
1d-control zero    = ZAction
1d-control (suc s) = SAction

1d-step : (x : 1d-state) → 1d-control x → 1d-state
1d-step zero ZR = 1
1d-step zero ZS = zero
1d-step (suc x) SL = x
1d-step (suc x) SS = suc x
1d-step (suc x) SR = suc (suc x)

1d-system : SeqDecProc
1d-system = SDP 1d-state 1d-control 1d-step

left : Policy 1d-system
left zero = ZS
left (suc n) = SL

right : Policy 1d-system
right zero  = ZR
right (suc n) = SR

stay : Policy 1d-system
stay zero = ZS
stay (suc n) = SS

1d-example : Vec 1d-state 5
1d-example = trajectorySDProc 1d-system
               (right ∷ right ∷ stay ∷ left ∷ left ∷ []) 0

distance : ℕ → ℕ → ℕ
distance zero zero       = 0
distance zero (suc m)    = 1 + distance zero m
distance (suc n) zero    = 1 + distance n zero
distance (suc n) (suc m) = distance n m

1d-reward : (goal : 1d-state) → (x : 1d-state) → 1d-control x -> 1d-state -> ℕ
1d-reward goal x y next = goal ∸ distance goal next

1d-prob-system : ℕ → SeqDecProb
1d-prob-system n = SDProb 1d-state 1d-control 1d-step ℕ (1d-reward n)

1d-find-5-system : SeqDecProb
1d-find-5-system = SDProb 1d-state 1d-control 1d-step ℕ (1d-reward 5)

1d-find-10-system : SeqDecProb
1d-find-10-system = SDProb 1d-state 1d-control 1d-step ℕ (1d-reward 10)

2d-problem : (goal₁ goal₂ : ℕ) → SeqDecProb
2d-problem goal₁ goal₂ = productSDProb (1d-prob-system goal₁) (1d-prob-system goal₂)

getcontrols : (state : 1d-state) → List (1d-control state)
getcontrols zero = ZS ∷ ZR ∷ []
getcontrols (suc state₁) = SL ∷ SS ∷ SR ∷ []

defaultcontrols : (state : 1d-state) → 1d-control state
defaultcontrols zero = ZS
defaultcontrols (suc state₁) = SS

testrun : (n goal : ℕ) → Vec 1d-state n
testrun n goal = trajectory (1d-prob-system goal) 10 (backwardsInduction2 n (1d-prob-system goal) getcontrols defaultcontrols)

cart : {A B : Set} → List A → List B → List (A × B)
cart [] l₂ = []
cart (a ∷ l₁) l₂ = listmap (λ b → a , b) l₂ ++ cart l₁ l₂

2d-getcontrols : (goal₁ goal₂ : ℕ) → (state : getstate (2d-problem goal₁ goal₂)) → List (getcontrol (2d-problem goal₁ goal₂) state)
2d-getcontrols goal₁ goal₂ (l , r) = cart (getcontrols l) (getcontrols r)

2d-defaultcontrols : (goal₁ goal₂ : ℕ) → (state : getstate (2d-problem goal₁ goal₂)) → getcontrol (2d-problem goal₁ goal₂) state
2d-defaultcontrols goal₁ goal₂ (l , r) = defaultcontrols l , defaultcontrols r

test2drun : (n goal₁ goal₂ : ℕ) → Vec (getstate (2d-problem goal₁ goal₂)) n
test2drun n goal₁ goal₂ = trajectory
                            (2d-problem goal₁ goal₂)
                            (0 , 0)
                            (backwardsInduction2
                              n
                              (2d-problem goal₁ goal₂)
                              (2d-getcontrols goal₁ goal₂)
                              (2d-defaultcontrols goal₁ goal₂))
