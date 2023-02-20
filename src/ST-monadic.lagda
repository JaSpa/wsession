\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- required for IO -}
open import Level using (Level) renaming (zero to lzero)

module ST-monadic where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; _+_; 0ℤ; -_)
open import Data.Product using (_×_; Σ; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)

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

open import Function.Base using (case_of_; _∘_; _∘′_; const; id; _$_)

open import IO.Base using (IO)

pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []

variable n k : ℕ

postulate
  Channel : Set
  primAccept : IO Channel
  primClose : Channel → IO {lzero} ⊤
  primSend : ∀ {A : Set} → A → Channel → IO {lzero} ⊤
  primRecv : ∀ {A : Set} → Channel → IO A


data Type : Set where
  nat int bool : Type

data Session : Set where
  ⊕′ &′ : ∀ {k} → (si : (i : Fin k) → Session) → Session
  send recv : Type → Session → Session
  end : Session

pattern ⁇_∙_ t s = recv t s
pattern ‼_∙_ t s = send t s

infixr 20 ‼_∙_ ⁇_∙_

vec→fin : Vec Session k → (Fin k → Session)
vec→fin {k = zero} [] = λ()
vec→fin {k = suc k} (x ∷ v) = λ where
  zero → x
  (suc i) → vec→fin v i

⊕ : Vec Session k → Session
⊕ = ⊕′ ∘ vec→fin

& : Vec Session k → Session
& = &′ ∘ vec→fin
  
-- service protocol for a binary function
binaryp : Session
binaryp = (recv int (recv int (send int end)))

-- service protocol for a unary function
unaryp : Session 
unaryp = (recv int (send int end))

-- service protocol for choosing between a binary and a unary function
arithp : Session
arithp = & [ binaryp , unaryp ]

variable
  a b : Level
  A A′ A″ A₁ A₂ : Set
  t : Type
  s s₁ s₂ : Session
  M : Set a → Set b

T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ
T⟦ bool ⟧ = Bool
T⟦ int ⟧ = ℤ
\end{code}
\newcommand\mstCommand{%
\begin{code}
data Command (A : Set) : Session → Set₂ where
  END    : Command A end
  SKIP   : (∀ {M : Set → Set₁} → {{RawMonad M}} → StateT A M ⊤)
    → Command A s → Command A s
  SEND   : (∀ {M : Set → Set₁} → {{RawMonad M}} → StateT A M T⟦ t ⟧)
    → Command A s → Command A (send t s)
  RECV   : (∀ {M : Set → Set₁} → {{RawMonad M}} → (T⟦ t ⟧ → StateT A M ⊤))
    → Command A s → Command A (recv t s)
  SELECT : ∀ {si} → (i : Fin k) → Command A (si i) → Command A (⊕′ si)
  CHOICE : ∀ {si} → ((i : Fin k) → Command A (si i)) → Command A (&′ si)
\end{code}}
\newcommand\mstExampleServers{%
\begin{code}
addp-command : Command ℤ binaryp
addp-command = RECV put $ RECV (modify ∘′ _+_) $ SEND get $ END

negp-command : Command ℤ unaryp
negp-command = RECV (put ∘ -_) $ SEND get $ END

arithp-command : Command ℤ arithp
arithp-command = CHOICE λ where
  zero → addp-command
  (suc zero) → negp-command
\end{code}}
\newcommand\mstExecutor{%
\begin{code}
exec : {s : Session} → Command A s → StateT A (ReaderT Channel IO) ⊤
exec END             = ask >>= liftIO ∘ primClose
exec (SKIP act cmd)  = act >> exec cmd
exec (SEND getx cmd) = getx >>= λ x → ask >>= liftIO ∘ primSend x >> exec cmd
exec (RECV putx cmd) = ask >>= liftIO ∘ primRecv >>= putx >> exec cmd
exec (SELECT i cmd)  = ask >>= liftIO ∘ primSend i >> exec cmd
exec (CHOICE f-cmd)  = ask >>= liftIO ∘ primRecv >>= λ x → exec (f-cmd x)
\end{code}}
\newcommand\mstAcceptor{%
\begin{code}[hide]
record Accepting A s : Set₂ where
  constructor ACC
  field pgm : Command A s

acceptor : Accepting A s → A → IO A
acceptor (ACC pgm) a = do
  ch ← primAccept
  ⟨ final , _ ⟩ ← runReaderT (runStateT (exec pgm) a) ch
  pure final
\end{code}}
