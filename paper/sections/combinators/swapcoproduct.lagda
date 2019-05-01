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

  surrCoproduct :  (p1 : SDProc) -> (p2 : SDProc) ->
                   swap p1 p2 -> swap p2 p1 -> SDProc
  surrCoproduct (SDP S1 C1 sf1) (SDP S2 C2 sf2) sw1 sw2 =
  record {

    State    = S1 sumuni S2;
    Control  = \ {  (inl s)           -> Maybe (C1 s);
                    (inr s)           -> Maybe (C2 s)};
    step     = \ {  (inl s) nothing   -> inr (sw1 s);
                    (inl s) (just c)  -> inl (sf1 s c);
                    (inr s) nothing   -> inl (sw2 s);
                    (inr s) (just c)  -> inr (sf2 s c)}}
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
