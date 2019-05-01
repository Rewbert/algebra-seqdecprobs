% -*- latex -*-

\section{Examples}
\label{sec:examples}


As an example, let us consider a sequential decision process where the state space is a one dimensional coordinate system represented by natural numbers.
%

\begin{code}
  oned-state  :  Set
  oned-state  =  Nat
\end{code}

%
There are generally three available controls, taking a step to the left, staying or taking a step to the right.
%
Here taking a step to the left means subtracting one from the coordinate, stay means not changing it at all and taking a step to the right means incrementing it by one.
%

\begin{code}
  data SAction : Set where
    SL  : SAction -- left
    SS  : SAction -- stay
    SR  : SAction -- right
\end{code}

%
However, there is an edge case.
%
When the state is zero, it is not possible to take a step to the left, and so there are only two available controls.
%

\begin{code}
  data ZAction : Set where
    ZS  : ZAction -- stay
    SR  : ZAction -- right
\end{code}

%
We can encode this behaviour since the control is depending on the state.
%
If the state is zero, the available controls are those defined in the |ZAction| data type.
%
Otherwise the available controls are those defined in the |SAction| data type.
%

\begin{code}
  oned-control  :  oned-state -> Set
  oned-control zero     = ZAction
  oned-control (suc n)  = SAction
\end{code}

%
The step functions is swiftly implemented, pattern matching on the states and controls.
%
\begin{code}
  oned-step  :  (x : oned-state) -> oned-control x -> oned-state
  oned-step  zero     ZR  = 1
  oned-step  zero     ZS  = 0
  oned-step  (suc n)  SL  = n
  oned-step  (suc n)  SS  = suc n
  oned-step  (suc n)  SR  = suc (suc n)
\end{code}
%
Finally, a sequential decision process can be defined.
%
\begin{code}
  system  :  SDProc
  system  =  SDP oned-state oned-control oned-step
\end{code}

%
Now, how to turn a process into a problem?
%
We need to introduce some sort of goal, described by a |reward| function.
%
For our example we define the reward function to be parameterised over a target coordinate.
%
The reward function could then reward a proposed step based on how close to the target it lands.
%
\begin{code}
  large-number : Nat
  large-number = 10000

  oned-reward :  oned-state ->
                 (x : oned-state) -> oned-control x -> oned-state -> Nat
  oned-reward target x0 y x1 = large-number - (distance target x1)
\end{code}
%
We can redefine the sequential decision process above to be a sequential decision problem simply by instantiating the |SDProb| record.
%

\begin{code}
  problem : oned-state -> SDProb
  problem target = SDProb oned-state oned-control oned-step (oned-reward target)
\end{code}
