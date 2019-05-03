% -*- latex -*-

\subsection{Dynamic System}
\label{subsec:dynsys}

%if false
\begin{code}

module dynamicsystem where
open import Data.Nat
open import Data.Vec

\end{code}
%endif

%
A dynamic system is a system which at any given time has a |State|.
%
The system can walk through a series of states by making use of a transition function.
%
This description of a system can be described as a record in Agda.
%
\begin{code}
record DynamicSystem : Set1 where
  field
    State  : Set
    step   : State -> State
\end{code}
%
To make further type signatures more convenient it is handy to define helper functions which extract the different components of the record.
%
\begin{code}
getstate : DynamicSystem -> Set
getstate system = DynamicSystem.State system
\end{code}
%if false
\begin{code}
getstep : (x : DynamicSystem) → (getstate x → getstate x)
getstep = DynamicSystem.step
\end{code}
%endif

%
In the following sections these helper functions are assumed to exist without being explicitly mentioned in this text.
%
Computing a sequence of states should come naturally to the functional programmer.
%
We define a recursive function that at each step computes the next state.
%

\begin{code}
trajectory :   (sys : DynamicSystem) ->  (getstate sys)  ->
               (n : ℕ) -> Vec (getstate sys) n
trajectory system x0 zero     = []
trajectory system x0 (suc n)  = x0 ∷ trajectory system x1 n
  where  x1  :  getstate system
         x1  =  getstep system x0
\end{code}

\cite{ionescu2009vulnerability}
\TODO{cite cezar ionescu thesis}
% reference to Cezars thesis (ask patrik how to reference it properly)  https://refubium.fu-berlin.de/handle/fub188/5259
