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
Looking back at the example of the one dimensional coordinate system, we find ourselves wondering if we would now get a process of a two dimensional coordinate system seemingly for free.
%
The answer, unsurprisingly, is yes.
%
\begin{code}
twod-system = oned-system ×SDP oned-system
\end{code}

%
In section \ref{sec:policycombinators} we introduce combinators for policy sequences.
%
Here we use the product combinator to produce a policy sequence that is compatible with the new process.
%
\begin{code}
twodsequence :  PolicySeq twod-system 5
twodsequence =  zipWith _×P_ pseq pseq
\end{code}
%
And now we can evaluate this new process like we did with the one dimensional system.
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
