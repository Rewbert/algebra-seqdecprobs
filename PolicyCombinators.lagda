\begin{code}
module PolicyCombinators where

open import Data.Nat
open import Data.Vec
open import Data.Product
open import Data.Sum

open import SeqDecProc
open import Bellman
\end{code}

\begin{code}
ProductPolicy : {x y : SeqDecProc} → {n : ℕ} → PolicySeq x n → PolicySeq y n → PolicySeq (productSDProc x y) n
ProductPolicy = zipWith (λ p₁ → λ p₂ → λ pstate → p₁ (proj₁ pstate) , p₂ (proj₂ pstate))

SumPolicy : {x y : SeqDecProc} → {n : ℕ} → PolicySeq x n → PolicySeq y n → PolicySeq (sumSDProc x y) n
SumPolicy = zipWith (λ p₁ → λ p₂ → λ { (inj₁ x) → p₁ x ;
                                         (inj₂ y) → p₂ y})

getstate = SeqDecProc.State
getcontrol = SeqDecProc.Control
getstep  = SeqDecProc.Step

stepfun : (x : SeqDecProc) → Set
stepfun x = (st : getstate x) → getcontrol x st → getstate x

sumSF : {x y : SeqDecProc} → stepfun (sumSDProc x y) → (stepfun x × stepfun y)
sumSF f = (λ state → λ control → {!Not possible as f will return a state!}) ,
          (λ state → λ control → {!which is the sum of the two other states!})

\end{code}
