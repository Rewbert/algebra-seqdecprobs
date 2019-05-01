\begin{code}
module VSDProb where

open import Data.Nat
open import Data.List
open import Data.Vec hiding (map; _++_; foldl)
open import Data.Product hiding (map)
open import Data.Bool

record Num (A : Set) : Set₁ where
  constructor [_,_,_]
  field
    unit : A
    _:+:_ : A → A → A
    _:≤:_ : A → A → Bool

combine_and_from_ : {A : Set} → A → A → Num A → A
combine a and b from [ _ , _:+:_ , _ ] = a :+: b

compare_and_from_ : {A : Set} → A → A → Num A → Bool
compare a and b from [ _ , _ , _:≤:_ ] = a :≤: b

record VSeqDProb A : Set₁ where
  constructor VSDProb
  field
    State   : Set
    Control : State -> Set
    step    : (x : State) -> (y : Control x) -> State
    Val     : Num A
    reward  : (x : State) -> (y : Control x) -> (x' : State) -> A

    {- The control space is finite, and it is always possible to retrieve all controls
       available in a given state. -}
    finite-controls : (x : State) → List (Control x)

    {- Furthermore, there are no states that have no possible controls. -}
    progression     : (x : State) → Control x

{- helper functions, makes acessing elements prettier -}
getstate   = VSeqDProb.State
getcontrol = VSeqDProb.Control
getstep    = VSeqDProb.step
getval     = VSeqDProb.Val
getreward  = VSeqDProb.reward
getfincont = VSeqDProb.finite-controls
getprog    = VSeqDProb.progression

cart : {A B : Set} → List A → List B → List (A × B)
cart [] l₂ = []
cart (x ∷ l₁) l₂ = map (λ s → x , s) l₂ ++ cart l₁ l₂

productVSDProb : {A : Set} → VSeqDProb A → VSeqDProb A → VSeqDProb A
productVSDProb
  (VSDProb s₁ c₁ sf₁ Val rf₁ fc₁ p₁)
  (VSDProb s₂ c₂ sf₂ Val₁ rf₂ fc₂ p₂) =
   VSDProb (s₁ × s₂)
     (λ state → c₁ (proj₁ state) × c₂ (proj₂ state))
     (λ state → λ control →
          sf₁ (proj₁ state) (proj₁ control) ,
          sf₂ (proj₂ state) (proj₂ control))
     Val
     (λ state → λ control → λ next →
       combine rf₁ (proj₁ state) (proj₁ control) (proj₁ next)
       and     rf₂ (proj₂ state) (proj₂ control) (proj₂ next)
       from Val)
     (λ state → cart (fc₁ (proj₁ state)) (fc₂ (proj₂ state)))
      λ state → p₁ (proj₁ state) , p₂ (proj₂ state)

{- Policy takes a state and returns a control for that state. -}
Policy : {A : Set} → VSeqDProb A → Set
Policy (VSDProb State Control _ _ _ _ _ ) = (x : State) → Control x

{- A policy sequence is simply a vector of such policies. -}
PolicySeq : {A : Set} → VSeqDProb A → ℕ → Set
PolicySeq x n = Vec (Policy x) n

{- Given a problem, a state for that problem and a function which can give a value
   for each of the controls available for that state, returns the maximum available
   value possible to obtain. -}
max : {A : Set} → (x : VSeqDProb A) → (state : getstate x) → (getcontrol x state → A) → A
max x state f = foldl (λ val
                    → λ control → if compare val and f control from getval x
                                    then f control
                                    else val)
                      (Num.unit (getval x))
                      allcontrols
  where allcontrols : List (getcontrol x state)
        allcontrols = getfincont x state

{- Similarly as above, but returns the control which gives this optimal value. -}
argmax : {A : Set} → (x : VSeqDProb A) → (state : getstate x) → (getcontrol x state → A) → getcontrol x state
argmax x state f = foldl (λ current → λ contender → if compare f current and f contender from getval x
                                                      then contender
                                                      else current)
                         (getprog x state)
                         allcontrols
  where allcontrols : List (getcontrol x state)
        allcontrols = getfincont x state

val : {A : Set} → {n : ℕ} → (x : VSeqDProb A) → (state : getstate x) → PolicySeq x n → A
val x state []          = Num.unit (getval x)
val x state (y ∷ seq) = combine getreward x state (y state) x'
                         and val x x' seq
                         from getval x
  where x' : getstate x
        x' = getstep x state (y state)

optExt : {A : Set} → {n : ℕ} → (x : VSeqDProb A) → PolicySeq x n → Policy x
optExt {A} x ps state = argmax x state f
  where f : getcontrol x state → A
        f y = combine getreward x state y (getstep x state y)
              and val x (getstep x state y) ps
              from getval x

backwardsInduction : {A : Set} → (n : ℕ) → (x : VSeqDProb A) → PolicySeq x n
backwardsInduction zero x    = []
backwardsInduction (suc n) x = optExt x ps ∷ ps
  where ps : PolicySeq x n
        ps = backwardsInduction n x
\end{code}
