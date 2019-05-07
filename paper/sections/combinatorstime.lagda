% -*- latex -*-
\section{Combinators for the Time Dependent Case}
\label{sec:combinatorstime}

%if false
\begin{code}
module combinatorstime where

open import core.seqdecproctime
open import combinators
open import Data.Nat
open import Data.Product
open import Data.Sum
\end{code}
%endif


\begin{code}
Pred' : Pred ℕ → Set₁
Pred' S = (t : ℕ) → Pred (S t)

_×St_ : (S₁ S₂ : Pred ℕ) → Pred ℕ
s₁ ×St s₂ = λ t → s₁ t × s₂ t

_×Ct_ : {S₁ S₂ : Pred ℕ} → Pred' S₁ → Pred' S₂ → Pred' (S₁ ×St S₂)
s₁ ×Ct s₂ = λ time → λ state → s₁ time (proj₁ state) × s₂ time (proj₂ state)

Step' : (S : Pred ℕ) -> Pred' S -> Set
Step' S C = (t : ℕ) → (s : S t) -> C t s -> S (suc t)

_×sft_ :  {S₁ S₂ : Pred ℕ} → {C₁ : Pred' S₁} → {C₂ : Pred' S₂}
      →  Step' S₁ C₁ → Step' S₂ C₂ → Step' (S₁ ×St S₂) (C₁ ×Ct C₂)
sf₁ ×sft sf₂ = λ time → λ state → λ control →
  sf₁ time (proj₁ state) (proj₁ control) , sf₂ time (proj₂ state) (proj₂ control)

_×SDPT_ : SDProcT → SDProcT → SDProcT
SDPT S₁ C₁ sf₁ ×SDPT SDPT S₂ C₂ sf₂ = SDPT (S₁ ×St S₂) (C₁ ×Ct C₂) (sf₁ ×sft sf₂)
\end{code}

\begin{code}
_⊎St_ : (S₁ S₂ : Pred ℕ) → Pred ℕ
s₁ ⊎St s₂ = λ t → s₁ t ⊎ s₂ t

_⊎Ct_ : {S₁ S₂ : Pred ℕ} → Pred' S₁ → Pred' S₂ → Pred' (S₁ ⊎St S₂)
(C₁ ⊎Ct C₂) time = λ {  (inj₁ s₁) → C₁ time s₁ ;
                         (inj₂ s₂) → C₂ time s₂}

_⊎sft_ :  {S₁ S₂ : Pred ℕ} → {C₁ : Pred' S₁} → {C₂ : Pred' S₂}
       →  Step' S₁ C₁ → Step' S₂ C₂ → Step' (S₁ ⊎St S₂) (C₁ ⊎Ct C₂)
sf₁ ⊎sft sf₂ = λ time → λ {  (inj₁ s₁) → λ control → inj₁ (sf₁ time s₁ control) ;
                              (inj₂ s₂) → λ control → inj₂ (sf₂ time s₂ control)}

_⊎SDPT_ : SDProcT → SDProcT → SDProcT
SDPT S₁ C₁ sf₁ ⊎SDPT SDPT S₂ C₂ sf₂ = SDPT (S₁ ⊎St S₂) (C₁ ⊎Ct C₂) (sf₁ ⊎sft sf₂)
\end{code}
