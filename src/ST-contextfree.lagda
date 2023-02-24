\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- required for IO -}
module ST-contextfree where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc; toℕ; opposite)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; _+_; 0ℤ; -_)
open import Data.Product using (_×_; Σ; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)

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
infixr 30 _⨟′_ _⨟_ _⨟[_]_
infixl 40 ⁇_ ‼_
infixr 50 μ_ `_

variable t : Type
variable s s₁ s₂ : Session n

dual : Session n → Session n
dual (⁇ x) = ‼ x
dual (‼ x) = ⁇ x
dual (⊕′ si) = &′ (dual ∘ si)
dual (&′ si) = ⊕′ (dual ∘ si)
dual (s₁ ⨟ s₂) = dual s₁ ⨟ dual s₂
dual skip = skip
dual (μ s) = μ (dual s)
dual (` x) = ` x

vec→fin : Vec (Session n) k → (Fin k → Session n)
vec→fin {k = zero} [] = λ()
vec→fin {k = suc k} (x ∷ v) = λ where
  zero → x
  (suc i) → vec→fin v i

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
Monadic : ((Set → Set₁) → Set₁) → Set₂
Monadic f = ∀ {M : Set → Set₁} → {{RawMonad M}} → f M

syntax Monadic (λ M → X) = Monad M ⇒ X

data Cmd n (A : Set) : Session n → Set₂ where
  SKIP   : (Monad M ⇒ StateT A M ⊤) → Cmd n A skip
  SEND   : (Monad M ⇒ StateT A M T⟦ t ⟧) → Cmd n A (‼ t)
  RECV   : (Monad M ⇒ (T⟦ t ⟧ → StateT A M ⊤)) → Cmd n A (⁇ t)
  SELECT : ∀ {si} → (Monad M ⇒ StateT A M (Fin k))
                  → ((i : Fin k) → Cmd n A (si i))
                  → Cmd n A (⊕′ si)
  CHOICE : ∀ {si} → ((i : Fin k) → Cmd n A (si i)) → Cmd n A (&′ si)
  _⨟[_]_ : Cmd n A s₁ → (A → A → A) → Cmd n A s₂ → Cmd n A (s₁ ⨟ s₂)
  LOOP   : Cmd (suc n) A s → Cmd n A (μ s)
  CONTINUE : (i : Fin n) → Cmd n A (` i)
\end{code}}
\begin{code}[hide]
_⨟′_ : Cmd n A s₁ → Cmd n A s₂ → Cmd n A (s₁ ⨟ s₂)
cmd₁ ⨟′ cmd₂ = cmd₁ ⨟[ constᵣ ] cmd₂

CmdStore : ∀ n → Set → Set₂
CmdStore n A = (i : Fin n) → ∃[ s ] (Cmd (suc (toℕ (opposite i))) A s)

pop1 : ∀{n} → CmdStore (suc n) A → CmdStore n A
pop : CmdStore (suc n) A → (i : Fin (suc n)) → CmdStore (suc (toℕ (opposite i))) A

pop1 cms i with cms (suc i)
... | cms₁ rewrite toℕ-inject₁ (opposite i) = cms₁

pop {n} cms zero rewrite toℕ-fromℕ n = cms
pop {suc n} cms (suc i) = subst (λ H → CmdStore (suc H) _) (sym (toℕ-inject₁ (opposite i))) (pop (pop1 cms) i)

{-# TERMINATING #-} -- a lie
\end{code}
\newcommand\cstExec{%
\begin{code}
exec : Cmd n A s → CmdStore n A → StateT A (ReaderT Channel IO) ⊤
exec (SKIP act) cms = act
exec (cmd₁ ⨟[ h ] cmd₂) cms = do
  x₁ ← exec cmd₁ cms >> get
  x₂ ← exec cmd₂ cms >> get
  put (h x₁ x₂)
exec {n = n}{A = A}{s = μ s} (LOOP cmd) cms = exec cmd cms′
    where cms′ : CmdStore (suc n) A
          cms′ zero    rewrite toℕ-fromℕ n = ⟨ s , cmd ⟩
          cms′ (suc i) rewrite toℕ-inject₁ (opposite i) = cms i
exec {n = suc n} (CONTINUE i) cms
  with cms i
... | ⟨ s-i , cmd-i ⟩ = exec cmd-i (pop cms i)
\end{code}}
\begin{code}[hide]
exec (SEND getx) cms = getx >>= λ x → ask >>= liftIO ∘ primSend x
exec (RECV putx) cms = ask >>= liftIO ∘ primRecv >>= putx
exec (SELECT getl cont) cms = getl >>= λ x → exec (cont x) cms
exec (CHOICE cont) cms = ask >>= liftIO ∘ primRecv >>= λ x → exec (cont x) cms
-- exec (cmd₁ ⨟[ h ] cmd₂) cms = exec cmd₁ cms >> get >>= λ x₁ → exec cmd₂ cms >> get >>= λ x₂ → put (h x₁ x₂)

record Accepting A s : Set₂ where
  constructor ACC
  field pgm : Cmd zero A s

acceptor : Accepting A s → A → IO A
acceptor (ACC pgm) a = do
  ch ← primAccept
  ⟨ final , _ ⟩ ← runReaderT (runStateT (exec pgm (λ())) a) ch
  primClose ch
  pure final

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

addp-command : Cmd n ℤ binaryp
addp-command = RECV put ⨟′ (RECV (modify ∘′ _+_) ⨟′ SEND get)

negp-command : Cmd n ℤ unaryp
negp-command = RECV (put ∘ -_) ⨟′ SEND get

arithp-command : Cmd n ℤ arithp
arithp-command = CHOICE (λ{ zero → addp-command ; (suc zero) → negp-command})

-- a tree protocol
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

recvTree : Cmd zero IntTree treep
recvTree = LOOP $ CHOICE λ where
  zero → RECV (put ∘ Leaf)
  (suc zero) → CONTINUE zero ⨟[ Branch ] CONTINUE zero
\end{code}}
\begin{code}[hide]

checkTree : IntTree → Fin 2
checkTree (Leaf x) = zero
checkTree (Branch t₁ t₂) = suc zero

getLeaf : IntTree → ℤ
getLeaf (Leaf x) = x
getLeaf (Branch t t₁) = 0ℤ

getBranch : IntTree → IntTree × IntTree
getBranch (Leaf x) = ⟨ (Leaf 0ℤ) , (Leaf 0ℤ) ⟩
getBranch (Branch t₁ t₂) = ⟨ t₁ , t₂ ⟩

sendTree : Cmd zero IntTree (dual treep)
sendTree = LOOP  $ SELECT (pure checkTree <*> get) λ where
  zero → SEND (pure getLeaf <*> get)
  (suc zero) → {!!} ⨟[ {!!} ] {!!}

sendLeaf : ℤ → Cmd n ℤ (dual leafp)
sendLeaf x = SEND (pure x)

sendBranch : IntTree → IntTree → Cmd (suc n) ℤ (dual branchp)
sendBranch t₁ t₂ = {!!}


\end{code}
