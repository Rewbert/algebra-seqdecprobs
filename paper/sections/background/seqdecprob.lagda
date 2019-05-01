% -*- latex -*-
\subsection{Sequential Decision Problem}
\label{subsec:seqdecprob}
%
Again we can extend the notion of a |sequential decision process| to that of a |sequential decision problem| by introducing the idea of a reward obtained by transitioning from one state to another.
%
The problem becomes that of finding the sequence of policies which results in the highest sum of rewards.
%

\begin{code}
  record SDProb : Set1 where
    constructor SDProb
    field
      State    :  Set
      Control  :  State -> Set
      step     :  (x : State) -> Control x -> State
      Reward   :  (x : State) -> Control x -> State -> Nat
\end{code}

%
Policies for sequential decision |problems| are identical to those for sequential decision |processes|.
%
Consequently, policy sequences do neither them differ in their definition.
%
The only difference in their definition is that they must depend on a |SeqDecProb| and not a |SeqDecProc| in order to satisfy the typechecker, when used with sequential decision problems.
%
\begin{code}
  Policy : SDProb -> Set
  Policy (SDProb S C _ _)  =  (x : S) -> C x

  PolicySeq : SDProb -> Nat -> Set
  PolicySeq sys n = Vec (Policy sys) n
\end{code}

%
Now we have the proper definitions in place in order to explore how instances of such records can be combined, and what properties the resulting system would have.
%
