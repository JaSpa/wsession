\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- required for IO -}
module ST-indexed-contextfree where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ; opposite)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; _+_; 0ℤ; -_)
open import Data.Product using (_×_; Σ; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; lookup; take; drop)

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

open import Function.Base using (case_of_; _∘_; _∘′_; const; constᵣ; id; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; cong₂; trans; module ≡-Reasoning)

open import IO.Base using (IO)

open import Channels

open import Utils

pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []

variable n k : ℕ

data Type : Set where
  nat int : Type
\end{code}
\newcommand\cstSession{%
\begin{code}
data Session (n : ℕ) : Set where
  ⁇_ ‼_ : Type → Session n
  ⊕′ &′ : ∀ {k} → (si : (i : Fin k) → Session n) → Session n
  _⨟_ : Session n → Session n → Session n
  skip : Session n
  μ_ : Session (suc n) → Session n
  `_ : Fin n → Session n
\end{code}}
\begin{code}[hide]
-- infixr 30 _⨟′_
infixr 30 _⨟_ [_]_⨟[_]_[_]
infixl 40 ⁇_ ‼_
infixr 50 μ_ `_

variable t : Type
variable s s₁ s₂ : Session n
variable A₁ A₂ A′ B B₁ B₂ : Set

dual : Session n → Session n
dual (⁇ x) = ‼ x
dual (‼ x) = ⁇ x
dual (⊕′ si) = &′ (dual ∘ si)
dual (&′ si) = ⊕′ (dual ∘ si)
dual (s₁ ⨟ s₂) = dual s₁ ⨟ dual s₂
dual skip = skip
dual (μ s) = μ (dual s)
dual (` x) = ` x

⊕ : Vec (Session n) k → Session n
⊕ = ⊕′ ∘ vec→fin

& : Vec (Session n) k → Session n
& = &′ ∘ vec→fin


T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ
T⟦ int ⟧ = ℤ

\end{code}
\newcommand\cstCmd{%
\begin{code}
data Cmd {n} : Set → Set → Vec Set n → Vec Set n → Session n → Set₁ where
  SKIP      : ∀{V W} → (A → B) → Cmd A B V W s
  SEND      : ∀{V W} → (A → B × T⟦ t ⟧) → Cmd A B V W (‼ t)
  RECV      : ∀{V W} → (T⟦ t ⟧ → A → B) → Cmd A B V W (⁇ t)
  SELECT    : ∀ {V W}{si} {F : Fin k → Set}
    → (A → Σ (Fin k) F)
    → ((i : Fin k) → Cmd (F i) B V W (si i))
    → Cmd A B V W (⊕′ si)
  CHOICE    : ∀{V W} {si} → ((i : Fin k) → Cmd A B V W (si i)) → Cmd A B V W (&′ si)
  [_]_⨟[_]_[_] : ∀{V W} → (A → A₁ × A′) → Cmd A₁ B₁ V W s₁ → (A′ → B₁ → A₂) → Cmd A₂ B₂ V W s₂ → (B₁ → B₂ → B) → Cmd A B V W (s₁ ⨟ s₂)
  LOOP      : ∀{V W} → Cmd A B (A ∷ V) (B ∷ W) s → Cmd A B V W (μ s)
  CONTINUE  : ∀{V W} → (i : Fin n) → Cmd (lookup V i) (lookup W i) V W (` i)
\end{code}}
\begin{code}[hide]
_⨟′_ : ∀{C}{V W} → Cmd A B V W s₁ → Cmd B C V W s₂ → Cmd A C V W (s₁ ⨟ s₂)
cmd₁ ⨟′ cmd₂ = [ (λ x → ⟨ x , tt ⟩) ] cmd₁ ⨟[ constᵣ ] cmd₂ [ constᵣ ]

shrink : ∀ {n} → Vec Set n → (i : Fin n) → Vec Set (suc (toℕ (opposite i)))
shrink {n} V zero rewrite toℕ-fromℕ n = V
shrink {suc n} (x ∷ V) (suc i)  rewrite toℕ-inject₁ (opposite i) = shrink V i

CmdStore : ∀ n → Vec Set n → Vec Set n → Set₁
CmdStore n V W = (i : Fin n) → ∃[ s ] (Cmd {suc (toℕ (opposite i))} (lookup V i) (lookup W i) (shrink V i) (shrink W i) s)

pop1 : ∀ {V W} → CmdStore (suc n) (A ∷ V) (B ∷ W) → CmdStore n V W
pop1 cms i with cms (suc i)
... | cms₁ rewrite toℕ-inject₁ (opposite i) = cms₁

pop : ∀ {V W} → CmdStore (suc n) V W → (i : Fin (suc n)) → CmdStore (suc (toℕ (opposite i))) (shrink V i) (shrink W i)
pop {n} {V} {W} cms zero rewrite toℕ-fromℕ n = cms
pop {suc n} {A ∷ V} {B ∷ W} cms (suc i) rewrite toℕ-inject₁ (opposite i) = pop {n} {V} {W} (pop1 cms) i

{-# TERMINATING #-} -- a lie
\end{code}
\newcommand\cstExec{%
\begin{code}
exec : ∀{n}{A}{B}{V}{W}{s} → Cmd A B V W s → CmdStore n V W → A → (ReaderT Channel IO) B
exec (SKIP act) cms a = pure (act a)
exec (SEND getx) cms a = do
  let ⟨ b , x ⟩ = getx a
  ask >>= liftIO ∘ primSend x
  pure b
exec (RECV putx) cms a = do
  x ← ask >>= liftIO ∘ primRecv
  pure (putx x a)
exec (SELECT getx cont) cms a
  with getx a
... | ⟨ i , ai ⟩ = do
  ask >>= liftIO ∘ primSend i
  exec (cont i) cms ai
exec (CHOICE cont) cms a = do
  i ← ask >>= liftIO ∘ primRecv
  exec (cont i) cms a
exec [ split ] cmd₁ ⨟[ cross ] cmd₂ [ join ] cms a = do
  let ⟨ a₁ , a′ ⟩ = split a
  b₁ ← exec cmd₁ cms a₁
  let a₂ = cross a′ b₁
  b₂ ← exec cmd₂ cms a₂
  pure (join b₁ b₂)
exec{n}{A}{B}{V}{W}{s = μ s} (LOOP cmd) cms a = exec cmd cms′ a
    where cms′ : CmdStore (suc n) (A ∷ V) (B ∷ W)
          cms′ zero    rewrite toℕ-fromℕ n = ⟨ s , cmd ⟩
          cms′ (suc i) rewrite toℕ-inject₁ (opposite i) = cms i
exec{suc n} (CONTINUE i) cms a
  with cms i
... | ⟨ s-i , cmd-i ⟩ = exec cmd-i (pop cms i) a
\end{code}}
\begin{code}[hide]

record Accepting A B s : Set₁ where
  constructor ACC
  field pgm : Cmd A B [] [] s

acceptor : Accepting A B s → A → IO B
acceptor (ACC pgm) a = do
  ch ← primAccept
  b ← runReaderT (exec pgm (λ()) a) ch
  primClose ch
  pure b

-- examples

-- service protocol for a binary function
binaryp : Session n
binaryp = ⁇ int ⨟ ⁇ int ⨟ ‼ int

-- service protocol for a unary function
unaryp : Session n
unaryp = ⁇ int ⨟ ‼ int

-- service protocol for choosing between a binary and a unary function
arithp : Session n
arithp = & [ binaryp , unaryp ]

-- servers
variable V W : Vec Set n

addp-command : Cmd ⊤ ⊤ V W binaryp
addp-command = RECV const ⨟′ (RECV _+_ ⨟′ SEND (λ x → ⟨ tt , x ⟩))

negp-command : Cmd ⊤ ⊤ V W unaryp
negp-command = RECV (const ∘′ -_) ⨟′ SEND λ x → ⟨ tt , x ⟩

arithp-command : Cmd ⊤ ⊤ V W arithp
arithp-command = CHOICE λ where
  zero → addp-command
  (suc zero) → negp-command

-- -- a tree protocol
\end{code}
\newcommand\cstTreep{%
\begin{code}
data IntTree : Set where
  Leaf   : ℤ → IntTree
  Branch : IntTree → IntTree → IntTree

leafp : Session n
leafp = ⁇ int

branchp : Session (suc n)
branchp = ` zero ⨟ ` zero

treep : Session zero
treep = μ & [ leafp , branchp ]

recvTree : Cmd ⊤ IntTree [] [] treep
recvTree = LOOP $ CHOICE λ where
  zero → RECV (const ∘′ Leaf)
  (suc zero) → [ (λ x → ⟨ x , x ⟩) ] (CONTINUE zero) ⨟[ const ] (CONTINUE zero) [ Branch ]

IntTreeF : (Fin 2) → Set
IntTreeF zero = ℤ
IntTreeF (suc zero) = IntTree × IntTree

splitTree : IntTree → Σ (Fin 2) IntTreeF
splitTree (Leaf x) = ⟨ zero , x ⟩
splitTree (Branch t₁ t₂) = ⟨ (suc zero) , ⟨ t₁ , t₂ ⟩ ⟩

sendTree : Cmd IntTree ⊤ [] [] (dual treep)
sendTree = LOOP $ SELECT splitTree λ where
  zero → SEND (λ z → ⟨ tt , z ⟩)
  (suc zero) → [ id ] (CONTINUE zero) ⨟[ const ] (CONTINUE zero) [ const ]
\end{code}}

