% -*- latex -*-
\subsection{Interleaving processes}
\label{subsec:interleavingseqdecproc}
%
The next combinator is one that interleaves processes, allowing each of the two prior processes to progress one step at a time each.
%
This behaviour is similar to that of a game where two users take turns making their next move.
%
However, the users do not know what moves the other user has made, and can therefore not make particularly smart moves.
%
In section -insert section with policies- it is shown how computing optimal policies produce controls which do know of the other users move.

%
In the simplest case the number of combined processes is two, and a boolean can be used to see which of the two should be allowed to progress.
%
\begin{code}
  interleaveSDProc : SDProc -> SDProc -> SDProc
  interleaveSDProc (SDP S1 C1 sf1) (SDP S2 C2 sf2) =
  record {
    State    = Bool × (S1 × S2);
    Control  = \ {  (false , x1 , x2) -> C1 x1;
                    (true ,  x1 , x2) -> C2 s2};
    step     = \ {  (false , x1 , x2) -> \ control ->
                      true , sf1 x1 control , x2;
                    (true , x1 , x2) -> \ control ->
                      false , x1 , sf2 x2 control}}  
\end{code}

%
In this case the boolean acts as an index into the product, determining which system to progress.
%
This way of modeling the interleaved problem is not optimal, is combining more than two processes with it will produce undesired behaviour.
%
If we combine three processes using this combinator the resulting system would be one where one of the processes advance half the time, and the other two only a quarter of the time each.
%
If we instead consider an implementation where the input to the combinator is a vector of processes, we would construct a more clever process with a better indexing behaviour.
%
A system like this would let all the processes advance equally much.
%
\TODO{implement this - A general product type with an indexing function}
