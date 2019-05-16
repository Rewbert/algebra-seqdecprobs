% -*- latex -*-

%if false
\begin{code}
open import core.seqdecproc
open import examples
open import combinators
open import policycombinators

open import Data.Product hiding (map; zip)
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality
\end{code}
%endif
%
Looking back at the example of the one dimensional coordinate system, we find ourselves wondering if we would now get a process of a two dimensional coordinate system almost for free.
%
The answer, unsurprisingly, is yes.
%
\begin{code}
twod-system = oned-system ×SDP oned-system
\end{code}
%
In section \ref{sec:policycombinators} we will introduce combinators for policy sequences, but here we will not use them.
%TODO: why not use them? I was not sure if we were going to keep that section in. All the yellow-ness had me hesitating.
%\TODO{Find out if the section on policy combinators will be kept, and if so change the text to indicate that we are using a combinator defined later. Otherwise perhaps define this one combinator, as it is now, and use it for the example?}
We create a policy sequence for the twod-system by applying the previous policies componentwise to an inhabitant of the new product state.
%
% \TODO{rewrite this part}
\TODO{Perhaps show the "yellow" code + some workds about problems.}B
\begin{code}
twodsequence :  PolicySeq twod-system 5
twodsequence =  pseq ×Ps pseq
twodsequence =  zipWith  (λ { p1 p2 (s1 , s2) → (p1 s1 , p2 s2) })
                         pseq  pseq
\end{code}
%if False
\begin{code}
P : (S : Set) -> (S -> Set) -> Set
P S C = (x : S) -> C x
_×P'_  :  {S₁ S₂ : Set} -> {S₁ S₂ : Set} -> {C₁ : Pred S₁} -> {C₂ : Pred S₂}
      →  P S₁ C₁ → P S₂ C₂ → P (S₁ × S₂) (C₁ ×C C₂)
(p₁ ×P' p₂) (fst , snd) = (p₁ fst , p₂ snd)
twodsequence' : PolicySeq twod-system 5
twodsequence' =  zipWith (_×P'_) pseq pseq
\end{code}
%Some hidden argument problem: probably because |Policy system| does not evaluate which make it unclear to Agda at which types the ploci product is used..
%endif
%
And now we can evaluate this new process like we did with the oned system.
%
\begin{code}
runtwod = trajectory twod-system twodsequence

twodtest1 :  runtwod (0 , 5)
             ≡
             (0 , 4) ∷ (0 , 3) ∷ (1 , 4) ∷
             (1 , 4) ∷ (2 , 5) ∷ (2 , 5) ∷ []
twodtest1 = refl

twodtest2 :  runtwod (5 , 5)
             ≡
             (4 , 4) ∷ (3 , 3) ∷ (4 , 4) ∷
             (4 , 4) ∷ (5 , 5) ∷ (5 , 5) ∷ []
twodtest2 = refl
\end{code}
