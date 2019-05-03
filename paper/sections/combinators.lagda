% -*- latex -*-
\section{Combinators for sequential decision processes}
\label{sec:combsecdecproc}

%if false
\begin{code}
module combinators where

open import core.seqdecproc
open import Data.Nat
open import Data.Bool
open import Data.Product hiding (swap)
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Maybe

\end{code}
%endif

%
Now that we've seen a few examples and are getting comfortable with the notion of sequential decision problems, it is suitable to more forward and see what we can do with such problems.
%
This section will explore different ways sequential decision processes can be combined in order to produce more sophisticated processes.
%
%-----------------------------------------------------------------------
\subsection{Product}
\label{subsec:productseqdecproc}
%
A first example of how two problems can be combined is to create their product.
%
\TODO{Use consistent constructor/variable names/cases also elsewhere}
%
\begin{code}
productSDProc : SDProc → SDProc → SDProc
productSDProc (SDP S₁ C₁ sf₁)  (SDP S₂ C₂ sf₂) = record {
  State    = S₁ × S₂;
  Control  = \ { (s₁ , s₂) → C₁ s₁ × C₂ s₂ };
  step     = \ { (s₁ , s₂) → \ { (c₁ , c₂) → (sf₁ s₁ c₁ , sf₂ s₂ c₂) } }
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
  step     =  \ state -> \ control -> tt}
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

%
Looking back at our example with the one dimensional coordinate system, imagine we wish to define a process that acts in two dimensions.
%
This is now simply achieved by reusing the one dimensional process, supplying it twice to the product combinator.
% format this tomorrow morning
%> 2d-problem : SDProc
%> 2d-problem = productSDProc problem problem
%

%-----------------------------------------------------------------------
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
sumSDProc (SDP S1 C1 sf1) (SDP S2 C2 sf2) = record {
    State    = S1 ⊎ S2;
    Control  = \ {  (inj₁ s)    -> (C1 s);
                    (inj₂ s)    -> (C2 s)};
    step     = \ {  (inj₁ s) c  -> inj₁ (sf1 s c);
                    (inj₂ s) c  -> inj₂ (sf2 s c)}}
\end{code}

%
In the case of the product process the two prior processes were not entirely independent.
%
If one process could not progress the other process was affected in the sense that it too could not process further.
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
  State    = ⊥;
  Control  = \ state -> ⊥;
  step     = \ state -> \ control -> state }
\end{code}

%
Combining any process with the empty process using the coproduct combinator will produce a process that acts exactly as that of the given process.
%
There is no way to begin advancing the empty process, and so the only available option is to select an initial state from the other process and start progressing that.
%

%-----------------------------------------------------------------------
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
surrCoproduct (SDP S1 C1 sf1) (SDP S2 C2 sf2) sw1 sw2 = record {
  State    = S1 ⊎ S2;
  Control  = \ {  (inj₁ s)           -> Maybe (C1 s);
                  (inj₂ s)           -> Maybe (C2 s)};
  step     = \ {  (inj₁ s) nothing   -> inj₂ (sw1 s);
                  (inj₁ s) (just c)  -> inj₁ (sf1 s c);
                  (inj₂ s) nothing   -> inj₁ (sw2 s);
                  (inj₂ s) (just c)  -> inj₂ (sf2 s c)}}
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

%-----------------------------------------------------------------------
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
                  (true ,  x1 , x2) -> C2 x2};
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
%-----------------------------------------------------------------------

