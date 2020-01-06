% -*- Latex -*-

%if False
\begin{code}
module core.traj where

open import core.seqdecproc
open import Data.Nat
open import Data.Vec

\end{code}
%endif

\begin{code}
trajectory  :   (p : SDProc) -> {n : ℕ} ->
            ->  Vec (Policy (#st p) (#c p)) n
            ->  #st p ->  Vec (#st p) n
trajectory sys []        x0  = []
trajectory sys (p ∷ ps)  x0  = x1 ∷ trajectory sys ps x1
  where  x1  :  #st sys
         x1  =  (#sf sys) x0 (p x0)
\end{code}
