\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- required for IO -}
module Presentation where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; _+_; 0ℤ; -_)
open import Data.Product using (_×_; Σ; proj₁; proj₂; _,_) -- renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)

open import Function.Base using (case_of_; _∘_; _∘′_; const; id; _$_; _$′_)

open import Types

module the-monadic where
  open import IO.Base using (IO)
  -- stdlib 2.0!
  open import Data.Unit.Polymorphic.Base using (⊤; tt)

  open import Effect.Functor

  open import Effect.Monad
  open import Effect.Monad.State
  open import Effect.Monad.Reader.Transformer as Reader
  open import Effect.Monad.State.Transformer as State
  open import Effect.Monad.IO

  open import Effect.Monad.Reader.Instances
  open import Effect.Monad.State.Instances
  open import Effect.Monad.Identity.Instances
  open import Effect.Monad.IO.Instances
  open import IO.Instances

  open RawMonad {{...}}
  open RawMonadState {{...}}
  open RawMonadReader {{...}}
  open RawMonadIO {{...}}
  open RawFunctor {{...}}

  open import ST-monadic renaming (RECV to RECV′; SEND to SEND′; CLOSE to CLOSE′)

\end{code}
\newcommand\PresBinaryUnaryType{
\begin{code}
  S₁ = ⁇ int ∙ ‼ int ∙ end      -- server for unary function
  S₂ = ‼ int ∙ ⁇ int ∙ end      -- its dual
\end{code}}
\newcommand\PresUnaryMonadic{
\begin{code}
  negp-command′ : Cmd ℤ (⁇ int ∙ ‼ int ∙ end)
  negp-command′ = RECV′ (put ∘ -_) $ SEND′ get $ CLOSE′
\end{code}}
\begin{code}[hide]
module the-non-monadic where
  open import ST-finite-nonbranching hiding (negp-command; arithp)
  open import Data.Unit using (⊤; tt)
  open import Utils
  open import IO
  open import Channels IO ⊤
\end{code}
\newcommand\PresNegpCommand{
\begin{code}
  negp-command : Cmd ℤ (⁇ int ∙ ‼ int ∙ end)
  negp-command =  RECV (λ x a → - x)
               $′ SEND (λ a → (a , a))
               $′ CLOSE
\end{code}}
\begin{code}[hide]
  _^_ : ∀ {ℓ} → Set ℓ → ℕ → Set ℓ
  A ^ zero  = A
  A ^ suc n = A × (A ^ n)

  ^-fin : ∀ {n}{ℓ}{A : Set ℓ} → A ^ n → Fin (suc n) → A
  ^-fin {zero} an zero = an
  ^-fin {suc n} (a , an) zero = a
  ^-fin {suc n} (a , an) (suc i) = ^-fin an i

  ⊕[_] : ∀ {n} → Session ^ n → Session
  ⊕[ sn ] = ⊕′ (^-fin sn)

  &[_] : ∀ {n} → Session ^ n → Session
  &[ sn ] = &′ (^-fin sn)

  arithp = &[ binaryp , unaryp ]
\end{code}
\begin{code}[hide]
module the-recursive where
\end{code}
\newcommand\PresRecSession{
\begin{code}
  data Session (n : ℕ) : Set where
    μ_ : Session (suc n) → Session n
    `_ : Fin n → Session n
\end{code}}
