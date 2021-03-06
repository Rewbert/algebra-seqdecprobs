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

%let submit = False
% \documentclass[sigplan,review,anonymous]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
\documentclass[sigplan]{acmart}%\settopmatter{printfolios=true,printccs=false,printacmref=false}

%% Conference information
%% Supplied to authors by publisher for camera-ready submission;
%% use defaults for review submission.
\acmConference[TyDe'19]{ACM SIGPLAN Workshop on Type-Driven Development}{August 18, 2019}{Berlin, Germany}
%\acmConference[TyDe'19]{Type-Driven Development}{August 18, 2019}{Berlin, Germany}
\acmYear{2019}
\acmISBN{} % \acmISBN{978-x-xxxx-xxxx-x/YY/MM}
\acmDOI{} % \acmDOI{10.1145/nnnnnnn.nnnnnnn}
\startPage{1}

\setcopyright{none} %**TODO
\bibliographystyle{ACM-Reference-Format}

%%% Standard definitions from the lhs2TeX installation
%include polycode.fmt
%%% Put your own formatting directives in a separate file
%include paper.format

\usepackage{graphicx}
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption}
\usepackage{hyperref}
% \usepackage{color}
\renewcommand\UrlFont{\color{blue}\rmfamily}
\usepackage{doi}

%for agda
\RequirePackage[T1]{fontenc}
\RequirePackage[utf8x]{inputenc}
\RequirePackage{ucs}

% macro for monus operator (credit: https://tex.stackexchange.com/questions/147788/monus-operator-macro)
\providecommand{\dotdiv}{% Don't redefine it if available
  \mathbin{% We want a binary operation
    \vphantom{+}% The same height as a plus or minus
    \text{% Change size in sub/superscripts
      \mathsurround=0pt % To be on the safe side
      \ooalign{% Superimpose the two symbols
        \noalign{\kern-.35ex}% but the dot is raised a bit
        \hidewidth$\smash{\cdot}$\hidewidth\cr % Dot
        \noalign{\kern.35ex}% Backup for vertical alignment
        $-$\cr % Minus
      }%
    }%
  }%
}

%manually added unicode characters
\DeclareUnicodeCharacter{8759}{::}
\DeclareUnicodeCharacter{8760}{\dotdiv}
\DeclareUnicodeCharacter{8644}{\rightleftarrows}
\DeclareUnicodeCharacter{7511}{^{t}}

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
%\mathchardef\mhyphen="2D

% -------------------------------------------------------------------------------
\begin{document}
\title{An Algebra of Sequential Decision Problems}
\subtitle{Technical Report}
% \author{Robert Krook\inst{1}\orcidID{0000-0003-3619-2975}
%    \and Patrik Jansson\inst{1,2}\orcidID{0000-0003-3078-1437}}
\author{Robert Krook}
\orcid{0000-0003-3619-2975}
\affiliation{
  \department{Computer Science and Engineering}
  \institution{University of Gothenburg}
  \country{Sweden}
}
%Note: double "@" in email to please lhs2tex
\email{guskrooro@@student.gu.se}

\author{Patrik Jansson}
\orcid{0000-0003-3078-1437}
\affiliation{
  \department{Computer Science and Engineering}
  \institution{Chalmers University of Technology}
  \country{Sweden}
}
\email{patrik.jansson@@chalmers.se}

%-------------------------------------------------------------------------------

%\begin{abstract}
%  \input{abstract.txt}

%\keywords{Functional Programming \and Domain Specific Languages.}
%\end{abstract}
\maketitle

%include sections/extabstract.lagda

% \paragraph{Acknowledgements.}
% %
% The reviewers suggested many improvements to the paper.

%------------------------------------------------------------------------------
%\newpage
\bibliography{paper}

\clearpage
%\appendix

\section{Technical Report}
\label{sec:technicalreport}
%
The rest of this report makes up the technical report.
%
The technical report describes further combinators, discusses time dependent processes and provide more thorough examples.
%

%
The work described in this text is the result of a project carried out at Gothenburg University by Robert Krook, under the supervision of Patrik Jansson.
%
Robert has worked independently and met once a week with Patrik over the course of 8 weeks to discuss progress, potential bottlenecks and what to do next.
%
Patrik has been an invaluable source of information, both regarding sequential decision problems and how to write a scientific text.
%
%include sections/examples.lagda
%------------------------------------------------------------------------------
%include sections/combinators.lagda
%------------------------------------------------------------------------------
%include sections/core/seqdecproctime.lagda
%------------------------------------------------------------------------------
%include sections/combinatorstime.lagda
%------------------------------------------------------------------------------
%include sections/policycombinators.lagda
%------------------------------------------------------------------------------
%include sections/conclusions.lagda
%------------------------------------------------------------------------------
% \newpage
% %include sections/appendix.lagda

\end{document}
