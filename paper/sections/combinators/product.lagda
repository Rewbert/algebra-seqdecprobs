% -*- latex -*-
\subsection{Product}
\label{subsec:productseqdecproc}
%
A first example of how two problems can be combined is to create their product.
%
\TODO{Use consistent constructor/variable names/cases also elsewhere}
%
\begin{code}
  productSDProc : SDProc -> SDProc -> SDProc
  productSDProc (SDP S1 C1 sf1) (SDP S2 C2 sf2) = record {
      State    =  S1 × S2;
      Control  =  \ state -> C1 (proj1 state) × C2 (proj2 state);
      Step     =  \ state -> \ control ->
                    ( sf1  (proj1  state)  (proj1  control)
                    , sf2  (proj2  state)  (proj2  control) )
      }
\end{code}
%
As the new state, the cartesian product of the two prior states is chosen.
%
The new control is the cartesian product of the prior controls.
%
An observation to be made here is that in order for the new system to exist in any state, it has to hold components of both prior states.
%
This has the consequence that if one of the prior processes do not have any states, the new problem may never exist in a state either.
%
Similarly, if one of the components reaches a point where there are no available controls, and thus can not progress, the other component will not be able to progress either.
%
% maybe some diagram here (i can whip up some examples on my ipad later)

%
The functional programmer will often find himself needing a unit, e.g when using |reduce| or other frequently appearing constructs from the functional paradigm.
%
Naturally, it would be convenient to define units for the combinators described in this script.
%

%
Consider a process that has only one state, one control for that state and a step function which takes the only state and the only control, and from that computes the same state.
%
\begin{code}
  singleton : SDProc
  singleton = record {
    State    =  ⊤;
    Control  =  \ state -> ⊤;
    Step     =  \ state -> \ control -> tt}
\end{code}
%
This could be considered to be a constant process, since the state is constant and the control space never changes.
%

%
Taking the product of any process and the singleton process would produce a system where the only change during each step is that of the process which is not the singleton.
%
Of course, the other process could itself be the singleton process also.
%
In this case the only change in each step is exactly that of the singleton process.
%
No change at all.
%
