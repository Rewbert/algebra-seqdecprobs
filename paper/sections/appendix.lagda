% -*- Latex -*-

\subsection{Appendix B}
\label{subsec:appendixb}

\subsubsection{Time dependent interleaved process}
\label{subsubsec:timedependentinterleavedprocess}

%
The time dependent interleaved combinator needs to compute a process that holds components of both processes.
%
However, as the step function produces a new state of the next time step, and we only advance one of the components, the state will hold components of times as indicated below.
%
> time  :    0    ->    1    ->    2    ->    3    ->
> state :  (0,0)  ->  (1,0)  ->  (1,1)  ->  (2,1)  ->  ...
%
We notice that the pattern is \emph{(half time + rem time, half time)}, and try to encode the new state as such.
%

%if false
\begin{code}
-- rem when div with 2
rem : ℕ → ℕ
rem 0              = 0
rem 1              = 1
rem (suc (suc n))  = rem n

half : ℕ → ℕ
half n = ⌊ n /2⌋
\end{code}
%endif
\begin{code}
_⇄S_ : (S₁ S₂ : Pred ℕ) → Pred ℕ
s₁ ⇄S s₂ = λ t → s₁ (half t + rem t) × s₂ (half t)
\end{code}
%
The new control can be computed by inspecting what the remainder of the time index is.
%
If the remainder is |zero|, we want to advance the first component of the state and therefore select the first components control space.
%
Correspondingly, if the remainder is one we want to advance the other and therefore select the second components control space.
%
\begin{code}
_⇄C_  :  {S₁ S₂ : Pred ℕ}
      →  Pred' S₁ → Pred' S₂ → Pred' (S₁ ⇄S S₂)
(C₁ ⇄C C₂) time (s₁ , s₂)
  with rem time | inspect rem time
(C₁ ⇄C C₂) time (s₁ , s₂) | zero     | p
  = C₁ (half time + zero) s₁
(C₁ ⇄C C₂) time (s₁ , s₂) | suc rem  | p
  = C₂ (half time) s₂
\end{code}
%
We get stuck when we try to implement the new step function.
%
As already mentioned in the text Agda does not recognise that if we advance the first component the second one can be left unchanged.
%
One approach to implement this could maybe be to let the state carry a proof that if the remainder is zero, incrementing the time index by one and then taking half of that is the same as the current time index.
%
Then perhaps Agda could see that leaving the second component unchanged is a valid thing to do.
%
Similar reasoning applies to changing the second component and leaving the first unchanged.
%
\begin{code}
_⇄sf_  :  {S₁ S₂ : Pred ℕ}
       →  {C₁ : Pred' S₁} {C₂ : Pred' S₂}
       →  Step S₁ C₁ → Step S₂ C₂
       →  Step (S₁ ⇄S S₂) (C₁ ⇄C C₂)
(sf₁ ⇄sf sf₂) time (s₁ , s₂) c
  with rem time | inspect rem time
(sf₁ ⇄sf sf₂) time (s₁ , s₂) c | zero | p
  = {!!} , {!s₂!}
(sf₁ ⇄sf sf₂) time (s₁ , s₂) c | one  | p
  = {!!} , {!!}
\end{code}

\subsection{Combining policy sequences}
\label{subsec:combiningpolicysequences}

%
In section \ref{subsec:policycombinators} we showed how to combine policies.
%
The policy combinators works very well with |zipWith|.
%
We did however also implement a function to combine sequences, where we could be very clear in the types what is actually happening.
%
The defining equation is the same as we used in section \ref{subsec:timedependentcase} to combine two sequences, |zipWith|.
%
When we use this combinator Agda will mark the usage as yellow and report errors of unsolved constraints.
%
\begin{code}
combineSeq  :  {p₁ p₂ : SDProc} {n : ℕ}
               {_:c:_ : SDProc → SDProc → SDProc}
            →  (Policy p₁ → Policy p₂ → Policy (p₁ :c: p₂))
            →  PolicySeq p₁ n → PolicySeq p₂ n
            →  PolicySeq (p₁ :c: p₂) n
combineSeq = zipWith
\end{code}




