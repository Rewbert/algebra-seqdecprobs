% -*- latex -*-
\subsection{Surrendering Coproduct}
\label{subsec:surrcoproductseqdecproc}
%
The example of the coproduct combinator gives rise to an idea of a combinator which act similarly but that is able to release control to the other process.
%
The coproduct begun progressing in a state belonging to one of the prior processes, and could never switch to the other process.
%
Considering a function that could map a state in one of the prior processes to one in the other prior process, the coproduct could be redesigned to allow one process to release control to the other.
%
This can be done by having the control be of the |Maybe| type.
%
\begin{code}
  swap : SDProc -> SDProc -> Set
  swap p1 p2 = getstate p1 -> getstate p2

  surrCoproduct : (p1 : SDProc) -> (p2 : SDProc) ->
  swap p1 p2 -> swap p2 p1 -> SDProc
  surrCoproduct (SDP s1 c1 sf1) (SDP s2 c2 sf2) sw1 sw2 =
  record {
    State = s1 V s2;
    Control = \ {
      (inl s1) -> Maybe (c1 s1);
      (inr s2) -> Maybe (c2 s2)};
    Step = \ {
      (inl s1) nothing -> inr (sw1 s1);
      (inl s1) (just c1) -> inl (sf1 s1 c1);
      (inr s2) nothing -> inl (sw2 s2);
      (inr s2) (just c2) -> inr (sf2 s2 c2)}}
\end{code}

%
If the control at any step is nothing, the system will switch to a state belonging to the other prior process by calling the |swap| function.
%

%
With a combinator as this one the system could model e.g software.
%
As an example, one process could model the run of some software, while the other could model the execution of a garbage collector.
%
When the process modeling the software reaches a point where garbage collection is required, there will be no controls available. The software will give up control to the garbage collector process.
%
When the garbage collector process is done, it will reach a state where there is nothing left for it to do, and it will surrender control to the software process again.
%