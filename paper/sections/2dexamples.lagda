% -*- latex -*-

%if false
\begin{code}
open import core.seqdecproc
open import examples
open import combinators
-- open import policycombinators

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
twod-system = system ×SDP system
\end{code}
%
In section \ref{sec:policycombinators} we will introduce combinators for policy sequences, but here we will not use them.
%
We create a policy sequence for the twod-system by applying the previous policies componentwise to an inhabitant of the new product state.
%
\begin{code}
twodsequence : PolicySeq twod-system 5
twodsequence =  map  (λ pair → λ state →
                    proj₁ pair (proj₁ state) , proj₂ pair (proj₂ state))
                (zip sequence sequence)
\end{code}
%
And now we can evaluate this new process like we did with the oned system.
%
\begin{code}
runtwod = trajectory twod-system twodsequence

twodtest1 :  runtwod (0 , 5)
             ≡
             (0 , 5) ∷ (0 , 4) ∷ (0 , 3) ∷ (1 , 4) ∷ (1 , 4) ∷ (2 , 5) ∷ []
twodtest1 = refl

twodtest2 :  runtwod (5 , 5)
             ≡
             (5 , 5) ∷ (4 , 4) ∷ (3 , 3) ∷ (4 , 4) ∷ (4 , 4) ∷ (5 , 5) ∷ []
twodtest2 = refl
\end{code}
