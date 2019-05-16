% -*- latex -*-
\subsection{Sequential Decision Problem}
\label{subsec:seqdecprob}

%if false
\begin{code}

module core.seqdecprob where
open import Data.Nat
open import Data.Vec

\end{code}
%endif

%
Again we can extend the notion of a |sequential decision process| to that of a |sequential decision problem| by introducing the idea of a reward obtained by transitioning from one state to another.
%
The problem becomes that of finding the sequence of policies which results in the highest sum of rewards.
%

\begin{code}
record SDProblem : Set1 where
  constructor SDProb
  field
    State    :  Set
    Control  :  State -> Set
    step     :  (x : State) -> Control x -> State
    reward   :  (x : State) -> Control x -> State -> ℕ
\end{code}

%
The types for policies and policy sequences for sequential decision |problems| are identical to those for sequential decision |processes|.
%
%if False
The only difference in their definition is that they must depend on a |SeqDecProb| and not a |SeqDecProc| in order to satisfy the typechecker, when used with sequential decision problems.
%
\begin{code}
Policy : SDProblem -> Set
Policy (SDProb S C _ _)  =  (x : S) -> C x

PolicySeq : SDProblem -> ℕ -> Set
PolicySeq sys n = Vec (Policy sys) n
\end{code}
%endif
%
Now we have the proper definitions in place in order to explore how instances of such records can be combined, and what properties the resulting system would have.
%
