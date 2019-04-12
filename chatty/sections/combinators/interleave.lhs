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
  interleaveSDProc (SDP s1 c1 sf1) (SDP s2 c2 sf2) =
  record {
    State = Bool x (s1 x s2);
    Control = \ { (false , x1 , x2) -> c1 x1;
                  (true ,  x1 , x2) -> c2 s2};
    Step = \ {(false , x1 , x2) -> \ control ->
                 true , sf1 x1 control , x2;
              (true , x1 , x2) -> \ control ->
                 false , x1 , sf2 x2 control}}
    
\end{code}