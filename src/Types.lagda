\begin{code}[hide]
module Types where

open import Data.Integer using (ℤ)
open import Data.Bool using (Bool)

\end{code}
\newcommand\stFiniteType{%
\begin{code}
data Type : Set where
  int : Type
  bool : Type
\end{code}}
\begin{code}[hide]
module type-formatting where
  postulate
\end{code}
\newcommand\stTypeInterpretationSignature{%
\begin{code}[inline]
    ⟦_⟧ : Type → Set
\end{code}}
\newcommand\stTypeInterpretation{%
\begin{code}
⟦_⟧ : Type → Set
⟦ int ⟧ = ℤ
⟦ bool ⟧ = Bool
\end{code}}
\begin{code}[hide]
variable T : Type
\end{code}
