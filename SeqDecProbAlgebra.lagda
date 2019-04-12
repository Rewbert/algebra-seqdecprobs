\documentclass{article}
\usepackage{agda}
\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{fancyvrb}
\DefineVerbatimEnvironment
  {code}{Verbatim}
  {} % Add options if i want them

\title{Analysing an Algebra of Sequential Decision Problems}
\author{..}
\date{April 2019}

\begin{document}

\maketitle

\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module SeqDecProbAlgebra where

open import Data.Nat
open import Agda.Builtin.Nat using (_==_; _+_)
open import Data.Bool hiding (_∨_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_; inj₁ to inl; inj₂ to inr)
open import Data.Maybe
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Vec

open import SeqDecProc
open import SeqDecProb

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
\end{code}

\end{document}
