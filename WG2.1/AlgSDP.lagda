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
\title{Algebra of Sequential Decision Problems}
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
  \frametitle{Policies}

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
\pause
\vspace{-1.2cm}% \vspace{-\abovedisplayskip}\vspace{-\belowdisplayskip}
\restorecolumns
\begin{code}
  Pol  = Policy State Control
  St   = State
\end{code}
\pause
Our example:
\begin{code}
oned-system  :  SDProc
oned-system  =  SDP oned-state oned-control oned-step
\end{code}

\end{frame}

\end{document}

\begin{tikzpicture}[y=.2cm, x=.7cm,font=\sffamily]
 	%axis
	\draw (0,0) -- coordinate (x axis mid) (10,0);
    	\draw (0,0) -- coordinate (y axis mid) (0,30);
    	%ticks
    	\foreach \x in {0,...,10}
     		\draw (\x,1pt) -- (\x,-3pt)
			node[anchor=north] {\x};
    	\foreach \y in {0,5,...,30}
     		\draw (1pt,\y) -- (-3pt,\y)
     			node[anchor=east] {\y};
	%labels
	\node[below=0.8cm] at (x axis mid) {MOPS};
	\node[rotate=90, above=0.8cm] at (y axis mid) {Power [mW]};

	%plots
	\draw plot[mark=*, mark options={fill=white}]
		file {div_soft.data};
	\draw plot[mark=triangle*, mark options={fill=white} ]
		file {div_ciu.data};
	\draw plot[mark=square*, mark options={fill=white}]
		file {div_ciu_oscar.data};
	\draw plot[mark=square*]
		file {div_ciu_oscar_extrapolated.data};

	%legend
	\begin{scope}[shift={(4,4)}]
	\draw (0,0) --
		plot[mark=*, mark options={fill=white}] (0.25,0) -- (0.5,0)
		node[right]{soft};
	\draw[yshift=\baselineskip] (0,0) --
		plot[mark=triangle*, mark options={fill=white}] (0.25,0) -- (0.5,0)
		node[right]{ciu};
	\draw[yshift=2\baselineskip] (0,0) --
		plot[mark=square*, mark options={fill=white}] (0.25,0) -- (0.5,0)
		node[right]{ciu + oscar};
	\draw[yshift=3\baselineskip] (0,0) --
		plot[mark=square*, mark options={fill=black}] (0.25,0) -- (0.5,0)
		node[right]{ciu + oscar extrapolated};
	\end{scope}
\end{tikzpicture}

% ----------------------------------------------------------------
\usetikzlibrary{arrows}
% ..
\begin{tikzpicture}[
    scale=5,
    axis/.style={very thick, ->, >=stealth'},
    important line/.style={thick},
    dashed line/.style={dashed, thin},
    pile/.style={thick, ->, >=stealth', shorten <=2pt, shorten
    >=2pt},
    every node/.style={color=black}
    ]
    % axis
    \draw[axis] (-0.1,0)  -- (1.1,0) node(xline)[right]
        {$G\uparrow/T\downarrow$};
    \draw[axis] (0,-0.1) -- (0,1.1) node(yline)[above] {$E$};
    % Lines
    \draw[important line] (.15,.15) coordinate (A) -- (.85,.85)
        coordinate (B) node[right, text width=5em] {$Y^O$};
    \draw[important line] (.15,.85) coordinate (C) -- (.85,.15)
        coordinate (D) node[right, text width=5em] {$\mathit{NX}=x$};
    % Intersection of lines
    \fill[red] (intersection cs:
       first line={(A) -- (B)},
       second line={(C) -- (D)}) coordinate (E) circle (.4pt)
       node[above,] {$A$};
    % The E point is placed more or less randomly
    \fill[red]  (E) +(-.075cm,-.2cm) coordinate (out) circle (.4pt)
        node[below left] {$B$};
    % Line connecting out and ext balances
    \draw [pile] (out) -- (intersection of A--B and out--[shift={(0:1pt)}]out)
        coordinate (extbal);
    \fill[red] (extbal) circle (.4pt) node[above] {$C$};
    % line connecting  out and int balances
    \draw [pile] (out) -- (intersection of C--D and out--[shift={(0:1pt)}]out)
        coordinate (intbal);
    \fill[red] (intbal) circle (.4pt) node[above] {$D$};
    % line between out og all balanced out :)
    \draw[pile] (out) -- (E);
\end{tikzpicture}
%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End: