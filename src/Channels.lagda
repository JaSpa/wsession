\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- required for IO -}
open import Level using (Level) renaming (zero to lzero)

module Channels where
-- stdlib 2.0!
open import Data.Unit.Polymorphic.Base using (⊤; tt) public

open import IO

variable A : Set

postulate
  Channel : Set
  primAccept : IO Channel
  primClose : Channel → IO {lzero} ⊤
  primSend : A → Channel → IO {lzero} ⊤
  primRecv : Channel → IO A
\end{code}
