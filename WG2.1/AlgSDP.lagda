\documentclass[notitlepage]{beamer}
\usepackage{tikz}
%%% Standard definitions from the lhs2TeX installation
%include polycode.fmt
%%% Put your own formatting directives in a separate file
%include ../paper/paper.format
%for agda
\RequirePackage[T1]{fontenc}
\RequirePackage[utf8x]{inputenc}
\RequirePackage{ucs}
\DeclareUnicodeCharacter{8759}{::}
\DeclareUnicodeCharacter{8760}{\dotdiv}
\DeclareUnicodeCharacter{8644}{\rightleftarrows}
\DeclareUnicodeCharacter{7511}{^{t}}
\setbeamertemplate{navigation symbols}{}
\title{AlgSDP: Algebra of Sequential Decision Problems}
\subtitle{formalised in Agda}
\author{Robert Krook \and \textbf{Patrik Jansson}}
\date{2020-01-06, WG2.1 \#79 in Otterlo, NL}
\begin{document}
\begin{frame}
\titlepage
\begin{abstract}
Sequential decision problems are a well established concept in decision theory, with the Bellman equation as a popular choice for describing them. Botta, Jansson, Ionescu have formalised the notion of such problems in Idris (presented by Jansson at \#75 Uruguay, by Botta at \#77  Brandenburg). Here we focus on an Algebra of SDPs (in Agda): combinators for building more complex SDPs from simpler ones.
\end{abstract}
% WG2.1 talk: 2017-02-20, Patrik Jansson, Sequential Decision Problems and Avoidability using Dependent Types
% WG2.1 talk: 2018-07-03, Nicola Botta, Specifications in Small and Large Contexts https://ifipwg21wiki.cs.kuleuven.be/pub/IFIP21/Brandenburg/slides_botta.pdf
\end{frame}

\begin{frame}
\frametitle{AlgSDP by example in one slide}

A 1D-coord. syst. with |ℕ| as state and |+1|, |0|, and |-1| as actions.

> p : SDProc

\pause
We define a product to enable reusing |p| in a 2D setting:

> _×SDP_ : SDProc → SDProc → SDProc
> p² = p ×SDP p

\pause
Both |p| and |p²| use a fixed state space, but we can also handle time dependent processes (for example |p'| of type |SDProcT|).

> _×SDPT_ : SDProcT → SDProcT → SDProcT
> embed : SDProc → SDProcT
> p²' = p' ×SDPT (embed p)
> p³ = p² ×SDP p

\pause
Final example: a process that moves either in 3D or in 2D.

> _⊎SDPT_ : SDProcT → SDProcT → SDProcT
> game = p²' ⊎SDPT (embed p³)

You could think of this as choosing a map in a game.
\end{frame}


% \begin{frame}
%   \frametitle{AlgSDP contributions}
%
% \end{frame}


\begin{frame}
  \frametitle{Example: 1-dimensional coordinate system}

\only<1-5>{
  \begin{tikzpicture}[
    arr/.style={thick, ->},
    ]
    \draw[arr] (0,0) -- coordinate (x axis mid) (6,0) node(xline)[right]{$\cdots$};
    % ticks
    \foreach \x in {0,...,5}
      \draw (\x,1pt) -- (\x,-3pt)
        node[anchor=north] {\x};
    \only<1-2>{\draw[arr] (0,1.5) -- (0,0.2) node[midway,right] {\only<2>{Right}}; }
    \only<3>{\draw[arr] (1,1.5) -- (1,0.2) node[midway,right] {Right};}
    \only<4>{\draw[arr] (2,1.5) -- (2,0.2) node[midway,right] {Left};}
    \only<5>{\draw[arr] (1,1.5) -- (1,0.2) node[midway,right] {Stay};}
  \end{tikzpicture}
}
\begin{code}
oned-state  :  Set
oned-state  =  ℕ
\end{code}

\onslide<2->{
\begin{code}
data oned-control : oned-state -> Set where
  Right  : {n : oned-state} -> oned-control n
  Stay   : {n : oned-state} -> oned-control n
  Left   : {n : oned-state} -> oned-control (suc n)
\end{code}
}

\only<6>{
\begin{code}
oned-step  :  (x : oned-state) -> oned-control x -> oned-state
oned-step x        Right  = suc x
oned-step x        Stay   = x
oned-step (suc x)  Left   = x
\end{code}
}
\end{frame}

\begin{frame}
  \frametitle{Sequential Decision Process}
\savecolumns
\begin{code}
record SDProc : Set1 where
  constructor SDP
  field
    State    : Set
\end{code}
\pause
\vspace{-1.2cm}% \vspace{-\abovedisplayskip}\vspace{-\belowdisplayskip}
\restorecolumns
\begin{code}
    Control  : State -> Set
\end{code}
\pause
\vspace{-1.2cm}% \vspace{-\abovedisplayskip}\vspace{-\belowdisplayskip}
\restorecolumns
\begin{code}
    step     : (x : State) -> Control x -> State
\end{code}
% \pause
% \vspace{-1.2cm}% \vspace{-\abovedisplayskip}\vspace{-\belowdisplayskip}
% \restorecolumns
% \begin{code}
%   Pol  = Policy State Control
%   St   = State
% \end{code}
\pause
Our example:
\begin{code}
oned-system  :  SDProc
oned-system  =  SDP oned-state oned-control oned-step
\end{code}

\end{frame}
\begin{frame}
  \frametitle{Sequential Decision Problem}

In a sequential decision \textbf{problem} there is also a fourth field |reward|:
\begin{code}
record SDProb : Set1 where
  constructor SDP
  field
    State    :  Set
    Control  :  State -> Set
    step     :  (x : State) -> Control x -> State
    reward   :  (x : State) -> Control x -> Val
\end{code}
(where |Val| is often |ℝ|).

%TODO: perhaps also Accessors for state, control and step function components: #st, #c, #sf

\begin{itemize}
\item The Seq. Dec. Problem is: find a sequence of controls that maximises the sum of rewards.
\item Or, in more realistic settings with uncertainty, finding a sequence of \emph{policies} which maximises the \emph{expected} reward.
\item Rewards, and problems, are not the focus of this talk but are mentioned for completeness.
\end{itemize}



\end{frame}
\begin{frame}
  \frametitle{Policy}

\only<1-2>{%
In general:
\begin{code}
Policy : (S : Set) → ((s : S) → Set) → Set
Policy S C = (s : S) → C s
\end{code}
}%
\pause%
\only<2-3>{%
Specialised:
%format invisible = "\quad \mbox{\onelinecomment}"
\begin{code}
oned-Policy  :  Set
oned-Policy  =  Policy oned-state oned-control
invisible    =  (x : oned-state) -> oned-control x
\end{code}
}%
\pause%
Example policies:
\begin{code}
right stay tryleft : oned-Policy
right    _        = Right
stay     _        = Stay
tryleft  zero     = Stay
tryleft  (suc s)  = Left
\end{code}
\pause
A family of policies (to move |towards| a particular goal coordinate):
\begin{code}
towards : ℕ -> oned-Policy
towards goal n with compare n goal
... | less _ _     = Right
... | equal _      = Stay
... | greater _ _  = Left
\end{code}
\end{frame}
%TODO perhaps introduce trajectory
%TODO show Plus and Times with illustrations
%TODO show code for them
\newcommand{\citet}[1]{}
\newcommand{\paragraph}[1]{#1}

%if False
\begin{code}
module extabstract where

open import Data.Nat
open import Data.Product
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import core.traj

open import examples using (oned-state; oned-control; oned-step; oned-system; tryleft; stay; right)
open import core.seqdecproc -- using (SDProc; #st_; #sf_)
open import combinators using (Con; Step)
open import policycombinators using (_×P_)

Val = ℕ
\end{code}
%endif

\begin{frame}
  \frametitle{Back to Processes - now with abbreviations}

\begin{code}
record SDProc : Set1 where
  constructor SDP
  field    State    : Set
           Control  : Con State
           step     : Step State Control
\end{code}

\begin{spec}
Con : Set → Set₁
Con S = S → Set

Step : (S : Set) -> Con S -> Set
Step S C = (s : S) -> C s -> S

Policy : (S : Set) → ((s : S) → Set) → Set
Policy S C = (s : S) → C s
\end{spec}
\end{frame}
\begin{frame}
  \frametitle{Trajectory}

% Given a list of policies to apply, one for each time step, we can compute the trajectory of a process from a starting state.
%
Here |#st|, |#c|, |#sf| extract the different components of an SDP.
%
%include ../paper/sections/core/traj.lagda
%

\textbf{Example:}
%
\begin{code}
pseq       = tryleft ∷ tryleft ∷ right ∷ stay ∷ right ∷ []
test1      = trajectory oned-system pseq 0
invisible  = 0 ∷ 0 ∷ 1 ∷ 1 ∷ 2 ∷ []
\end{code}
%
In an applied setting many trajectories would be computed to explore the system behaviour.
\end{frame}

%
% In this abstract we focus on non-monadic, time-independent, sequential decision processes, but the algebra extends nicely to the more general case.
%
\begin{frame}
  \frametitle{The Product of SDPs}

\begin{code}
_×SDP_ : SDProc → SDProc → SDProc
(SDP S₁ C₁ sf₁) ×SDP (SDP S₂ C₂ sf₂)
  = SDP (S₁ × S₂) (C₁ ×C C₂) (sf₁ ×sf sf₂)
\end{code}
\only<2-3>{
\vspace{-0.8cm}
\begin{code}
Con : Set → Set₁
Con S = S → Set
\end{code}
}
\only<2-3>{\vspace{-1cm}
\begin{code}
_×C_  :  {S₁ S₂ : Set} ->
         Con S₁ -> Con S₂ -> Con (S₁ × S₂)
(C₁ ×C C₂) (s₁ , s₂) = C₁ s₁ × C₂ s₂
\end{code}
}\only<3>{
\begin{code}
Step : (S : Set) -> Con S -> Set
Step S C = (s : S) -> C s -> S
\end{code}
}\only<3-4>{\vspace{-1cm}
\begin{code}
_×sf_  :   {S₁ S₂ : Set} {C₁ : Con S₁} {C₂ : Con S₂}
       ->  Step S₁ C₁ -> Step S₂ C₂
       ->  Step (S₁ × S₂) (C₁ ×C C₂)
(sf₁ ×sf sf₂) (s₁ , s₂) (c₁ , c₂) = (sf₁ s₁ c₁ , sf₂ s₂ c₂)
\end{code}
}
\only<4>{
%format P1 = P "_1"
%format P2 = P "_2"
\textbf{Example:} |P1 ×SDP P2|
\includegraphics{../paper/images/product.png}
% Note that |Policy (S₁ × S₂) (C₁ ×C C₂) = (s : (S₁ × S₂)) → (C₁ ×C C₂) s|
}
\end{frame}

\begin{frame}
  \frametitle{Product example}

Example:
%
\begin{code}
twod-system = oned-system ×SDP oned-system
\end{code}

Now |twod-system| is a process of two dimensions rather than one:

\begin{code}
pseq = tryleft ∷ tryleft ∷ right ∷ stay ∷ right ∷ []
twodsequence  = zipWith _×P_ pseq pseq
test2         = trajectory twod-system twodsequence (0 , 5)
invisible     =  (0 , 4) ∷ (0 , 3) ∷ (1 , 4) ∷ (1 , 4) ∷ (2 , 5) ∷ []
\end{code}
%
where |_×P_| is a combinator for policies.

\end{frame}

\begin{frame}{Zero and One}

\begin{code}
zero : SDProc
zero = record {
  State    = ⊥;
  Control  = λ state -> ⊥;
  step     = λ state -> λ control -> state }
\end{code}

\begin{code}
unit : SDProc
unit = record {
  State    =  ⊤;
  Control  =  λ state -> ⊤;
  step     =  λ state -> λ control -> tt}
\end{code}
\end{frame}
\begin{frame}
  \frametitle{Coproduct combinator}

\begin{code}
_⊎SDP_ : SDProc → SDProc → SDProc
SDP S₁ C₁ sf₁ ⊎SDP SDP S₂ C₂ sf₂
  = SDP (S₁ ⊎ S₂) (C₁ ⊎C C₂) (sf₁ ⊎sf sf₂)

_⊎C_  :  {S₁ S₂ : Set}
      →  Con S₁ → Con S₂ → Con (S₁ ⊎ S₂)
(C₁ ⊎C C₂) (inj₁ s₁)  = C₁ s₁
(C₁ ⊎C C₂) (inj₂ s₂)  = C₂ s₂

_⊎sf_  :   {S₁ S₂ : Set}
       ->  {C₁ : Con S₁} -> {C₂ : Con S₂}
       ->  Step S₁ C₁ -> Step S₂ C₂
       ->  Step (S₁ ⊎ S₂) (C₁ ⊎C C₂)
(sf₁ ⊎sf sf₂) (inj₁ s₁) c₁  = inj₁ (sf₁ s₁ c₁)
(sf₁ ⊎sf sf₂) (inj₂ s₂) c₂  = inj₂ (sf₂ s₂ c₂)
\end{code}
\end{frame}
\begin{frame}
  \frametitle{Coproduct combinator example}

Left injection:
  \includegraphics[width=.8\linewidth]{../paper/images/coproduct-inj1.png}

Right injection:
  \includegraphics[width=.8\linewidth]{../paper/images/coproduct-inj2.png}
\end{frame}

\begin{frame}{Yielding coproduct example}

Illustration: It is capable of switching between the two processes, as illustrated by the calls to |v1| and |v2|.

\includegraphics[scale=0.7]{../paper/images/yieldcoproduct.png}

With a combinator such as this one could you model e.g a two player game.

The processes would be the players and the combined process allows each to take turns making their next move.

\end{frame}
\begin{frame}{Yielding coproduct code}

\begin{code}
_⊎C+_  :  {S₁ S₂ : Set}
       →  Con S₁ → Con S₂ → Con (S₁ ⊎ S₂)
(C₁ ⊎C+ C₂) (inj₁ s₁) = Maybe (C₁ s₁)
(C₁ ⊎C+ C₂) (inj₂ s₂) = Maybe (C₂ s₂)
\end{code}

\begin{code}
_⇄_ : (S₁ S₂ : Set) → Set
s₁ ⇄ s₂ = (s₁ -> s₂) × (s₂ -> s₁)
\end{code}

\begin{code}
⊎sf+  :  {S₁ S₂ : Set} {C₁ : Con S₁} {C₂ : Con S₂}
      →  (S₁ ⇄ S₂)
      →  Step S₁ C₁ → Step S₂ C₂
      →  Step (S₁ ⊎ S₂) (C₁ ⊎C+ C₂)
⊎sf+ _          sf₁ sf₂  (inj₁ s₁)  (just c)  = inj₁ (sf₁ s₁ c)
⊎sf+ _          sf₁ sf₂  (inj₂ s₂)  (just c)  = inj₂ (sf₂ s₂ c)
⊎sf+ (v₁ , _ )  sf₁ sf₂  (inj₁ s₁)  nothing   = inj₂ (v₁ s₁)
⊎sf+ (_  , v₂)  sf₁ sf₂  (inj₂ s₂)  nothing   = inj₁ (v₂ s₂)

syntax ⊎sf+ r sf₁ sf₂  =  sf₁ ⟨ r ⟩ sf₂
\end{code}
\end{frame}
%

\begin{frame}{Summary}
  \begin{itemize}
  \item It is possible to implement an algebra of SDPs
  \item Products are immediately useful\\
\includegraphics[scale=0.4]{../paper/images/product.png}
  \item Plain coproducts --- not so much
  \item Many variants possible: yielding coproducts, interleaving product, etc.\\
\includegraphics[scale=0.4]{../paper/images/yieldcoproduct.png}
\includegraphics[scale=0.4]{../paper/images/interleave.png}


\end{itemize}
Time-depedent, monadic cases left as exercises for the audience;-)



\end{frame}
\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End: