% -*- latex -*-
%----------------------------------------------------------------------------
%
%  Title       :  An Algebra of Sequential Decision Problems
%  Conference: :  MPC 2019
%  Author(s)   :  Robert Krook, Patrik Jansson
%  Copyright   :  TBD
%  Created     :  2019-04-12
%
%  Purpose : Build up a library of combinators for creating SeqDecProbs.
%            In the process, understand the design space better.
%
%----------------------------------------------------------------------------

%let submit = True
\documentclass[runningheads]{llncs}
%%% Standard definitions from the lhs2TeX installation
%include polycode.fmt
%%% Put your own formatting directives in a separate file
%include paper.format


\usepackage{graphicx}
\usepackage{hyperref}
% \usepackage{color}
\renewcommand\UrlFont{\color{blue}\rmfamily}
\usepackage{doi}

%for agda
\RequirePackage[T1]{fontenc}
\RequirePackage[utf8x]{inputenc}
\RequirePackage{ucs}

\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{autofe}
\usepackage{agda}

%%% Some useful macros
%if submit
\newcommand{\todo}[2][?]{}
%else
\newcommand{\todo}[2][?]{\marginpar{\raggedright \tiny TODO: #2}}
%endif
\newcommand{\TODO}[1]{\todo{#1}}
\newcommand{\refSec}[1]{Sec. \ref{#1}}
\newcommand{\refSecs}[1]{Secs. \ref{#1}}
\newcommand{\refSecI}[1]{Section \ref{#1}}
\newcommand{\refSecsI}[1]{Sections \ref{#1}}
\newcommand{\refTab}[1]{Tab. \ref{#1}}

% \newcommand{\getstate}[1]{\ensuremath{\left||#1\right||}}
\newcommand{\getstate}[1]{\ensuremath{\##1}}

% -------------------------------------------------------------------------------
\begin{document}
\title{An Algebra of Sequential Decision Problems}
\author{Robert Krook\inst{1}\orcidID{TODO}
   \and Patrik Jansson\inst{1,2}\orcidID{0000-0003-3078-1437}}

%Note: double "@" in email to please lhs2tex

\institute{University of Gothenburg,
             \email{guskrooro@@student.gu.se}
      \and Chalmers University of Technology,
             \email{patrik.jansson@@chalmers.se}%, Computer Science and Engineering, SE-412 96 Göteborg, Sweden
}
\maketitle

%-------------------------------------------------------------------------------

\begin{abstract}
  \TODO{The abstract should briefly summarize the contents of the paper in 150--250 words.}
  \input{abstract.txt}

\keywords{Functional Programming \and Domain Specific Languages.}
\end{abstract}

%\setcounter{tocdepth}{2}
%\tableofcontents
%\todo{Remove ToC before submission.}
%\newpage

%------------------------------------------------------------------------------
%include sections/background/background.lagda
%------------------------------------------------------------------------------
%include sections/examples/examples.lagda
%------------------------------------------------------------------------------
%include sections/combinators/combinators.lagda
%------------------------------------------------------------------------------

% \paragraph{Acknowledgements.}
% %
% The reviewers suggested many improvements to the paper.

%------------------------------------------------------------------------------
\bibliographystyle{splncs04}
\bibliography{paper}

\end{document}
