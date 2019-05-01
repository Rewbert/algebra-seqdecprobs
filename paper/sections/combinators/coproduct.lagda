% -*- latex -*-
\subsection{Coproduct}
\label{subsec:coproductseqdecproc}
%
The coproduct of two processes can be created by taking the new state to be the coproduct of the prior states.
%
The control is depending on what injection the given state was constructed with.
%
If it was constructed using the first injection the new control is that of the corresponding prior control.
%
Similarly if it was constructed using the second injection, the control is that of the corresponding prior control.
%
\begin{code}
  sumSDProc : SDProc -> SDProc -> SDProc
  sumSDProc (SDP s1 c1 sf1) (SDP s2 c2 sf2)
  = record {
      State = s1 V s2;
      Control = \ { (inl s1) -> (c1 s1);
                    (inr s2) -> (c2 s2)};
      step = \ { (inl s1) c -> inl (sf1 s1 c);
                 (inr s2) c -> inr (sf2 s2 c)}}
\end{code}

%
In the case of the product process the two prior processes were not entirely independent.
%
In one process could not progress the other process was affected in the sense that it too could not process further.
%
The sum of two processes keeps the two problems truly independent.
%
In fact, the coproduct of two processes will start progressing from some initial state, and depending on which injection is used the other process will never advance.

%
A process that acts as a unit to the coproduct combinator is the empty process.
%
The process has no states, no controls and the step function will return its input state.
%
However, we will never be able to call the step function since we can not supply a state.
%
\begin{code}
  empty : SDProc
  empty = record {
    State = \bot;
    Control = \ state -> \bot;
    step = \ state -> \ control -> state }
\end{code}

%
Combining any process with the empty process using the coproduct combinator will produce a process that acts exactly as that of the given process.
%
There is no way to begin advancing the empty process, and so the only available option is to select an initial state from the other process and start progressing that.
%