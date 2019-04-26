% -*- latex -*-
%----------------------------------------------------------------------------
%
%  Title       :  So far just a skeleton
%  Conference: :  Something suitable (the example below is from a Haskell Symposium submission)
%  Author(s)   :  A few of us
%  Copyright   :  Often needs to be transferred
%  Created     :  starting date
%
%  Purpose     :  It is good to try to formulate a purpose early on.
%
%----------------------------------------------------------------------------

%let submit = True
%if submit
\documentclass[times,authoryear]{sigplanconf}
%else
\documentclass[preprint,times]{sigplanconf}
%endif

%%% Standard definitions from the lhs2TeX installation
%include polycode.fmt
%%% Put your own formatting directives in a separate file
%include paper.format

\usepackage{url}

%for agda
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{autofe}
\usepackage{agda}

%if techreport
\usepackage{TRtitlepage}
%endif

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

\toappear{}
\begin{document}

%-------------------------------------------------------------------------------

%if submit
%\conferenceinfo{Haskell'12,} {September 13, 2012, Copenhagen, Denmark.}
%\CopyrightYear{2012}
%\copyrightdata{978-1-4503-1574-6/12/09}
%elif not techreport
%\titlebanner{Preprint}
%\preprintfooter{Preprint}
%endif

%if techreport
\TRtitlepage
  {Analysing an Algebra of Sequential Decision Problems}             % argument 1 <= the title
  {Robert Krook} % argument 2 <= authors
  {}                                     % argument 3 <= report number
%else
\title{Analysing an Algebra of Sequential Decision Problems}

\authorinfo{name}
           {city, country}
           {\texttt{email}}

\maketitle
%endif

%-------------------------------------------------------------------------------

\begin{abstract}
  The abstract should describe in a short and catch way what the paper is about etc.
\end{abstract}

%%% Some venues require ACM classification categories - here is an example
\category{D.1.1}%
  {Programming Techniques}%
  {Applicative (Functional) Programming}%

\terms
design, languages, verification

\keywords
some, important, concepts, not already, mentioned, in the title

%------------------------------------------------------------------------------
%include sections/background/background.lagda
%------------------------------------------------------------------------------
%include sections/examples/examples.lagda
%------------------------------------------------------------------------------
%include sections/combinators/combinators.lagda
%------------------------------------------------------------------------------
\paragraph{Acknowledgements.} This research has been partially funded
by the (some project title + granting agency).
%
Somebody helped with something.
%
The reviewers suggested many improvements to the paper.

%------------------------------------------------------------------------------
\bibliographystyle{abbrvnat}
%%% Keep references in a separate bib-file
\bibliography{paper}

\end{document}
