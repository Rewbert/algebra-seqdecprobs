% -*- Latex -*.
\subsection{Conclusions and future work}
\label{subsec:conclusionsandfuturework}
%
We have shown that sequential decision processes can quite comfortably be combined.
%
Things start to get interesting when we consider writing new policies rather than combining existing policies.
%
As exemplified in section \ref{subsec:policycombinators} a policy for a product state is essentially a policy for one process parameterised over another.
%
This becomes particularly interesting when we look at the interleaved process where we only wish to advance one component but we now have information about the other also.
%
Using backwards induction to compute optimal policy sequences could perhaps use this extra information to produce very clever sequences.
%

%
There are many avenues left to explore for future work.
%
\begin{itemize}
  \item Here we have mainly focused on sequential decision |processes|, and not so much on |problems|. It is not entirely clear how problems should be combined. The problems need to offer the same type of reward, normalised to some range and then combined in some way. Even when the type of the reward is the natural numbers, combining them is not unambiguous as there are many ways to combine natural numbers.
  \item There are definitely many more combinators than those presented by us in this text. Here we focused mainly on generic combinators that required no additional information and then briefly touched the yielding coproduct, which did require additional information in order to switch processes.
  \item Both processes and problems can be parameterised over a monad. A processes step function can e.g produce a list of possible next states and associate a probability to each of them. Modeling such uncertainties vastly increases the amount of problems that can be modeled using this framework. When combining processes like these combining the step functions becomes less trivial.
  \item Many claims and ideas in this text has been described but not formalised. As an example the notion of a unit and its properties could be formalised, and then the units presented here could be proven to be correct units. We are also interested in implementing an n-ary combinator for the interleaved combinator, as well as an interleaved combinator for the time dependent case.
\end{itemize}
