% -*- latex -*-
\subsection{Product}
\label{subsec:productseqdecproc}
%
A first example of how two problems can be combined is to produce their product.
\TODO{ask patrik how to render the cross. Actually, how to render everything! My formatting is not respected, anywhere :c}
%
\begin{code}
  productSDProc : SDProc -> SDProc -> SDProc
  productSDProc (SDP s1 c1 sf1) (SDP s2 c2 sf2)
  = record {
      State   = s1 x s2;
      Control = \state -> c1 (fst state) x c2 (snd state);
      Step    = \state -> \control ->
        sf1 (fst state) (fst control) ,
        sf2 (snd state) (snd control)}
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
% maybe some diagram here

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
    State = \top;
    Control = \state -> \top;
    Step = \state -> \control -> tt}
\end{code}
%
This could be considered to be a constant process.
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