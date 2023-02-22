\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- required for IO -}
module ST-recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; toℕ; opposite)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Integer using (ℤ; 0ℤ; _+_; -_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)

open import Data.Unit using (⊤; tt)

open import Function.Base using (case_of_; _∘_; const; _$_; id)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; cong₂; trans; module ≡-Reasoning)

open import IO


pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []


variable
  n k : ℕ
\end{code}
\newcommand\rstFiniteType{%
\begin{code}
data Type : Set where
  int bool : Type
\end{code}}
\begin{code}[hide]
  nat : Type
  fin : ℕ → Type

module formatting1 where
\end{code}
\newcommand\rstBranchingType{%
\begin{code}
  data Session (n : ℕ) : Set where
    ⊕′ &′ : ∀ {k} → (si : (i : Fin k) → Session n) → Session n
\end{code}}
\newcommand\rstSession{%
\begin{code}
data Session (n : ℕ) : Set where
  ‼_∙_ ⁇_∙_ : Type → Session n → Session n
  end : Session n
  ⊕′ &′ : ∀ {k} → (si : (i : Fin k) → Session n) → Session n
  μ_ : Session (suc n) → Session n
  `_ : Fin n → Session n
\end{code}}
\begin{code}[hide]

pattern recv t s = ⁇ t ∙ s
pattern send t s = ‼ t ∙ s

infixr 20 ‼_∙_ ⁇_∙_
infixr 20 μ_ `_

vec→fin : Vec (Session n) k → (Fin k → Session n)
vec→fin {k = zero} [] = λ()
vec→fin {k = suc k} (x ∷ v) = λ where
  zero → x
  (suc i) → vec→fin v i

⊕ : Vec (Session n) k → Session n
⊕ = ⊕′ ∘ vec→fin

& : Vec (Session n) k → Session n
& = &′ ∘ vec→fin
  

-- service protocol for a binary function
binaryp : Session n → Session n
binaryp s = ⁇ int ∙ ⁇ int ∙ ‼ int ∙ s
-- service protocol for a unary function
-- service protocol for choosing between a binary and a unary function
arithp : Session n → Session n
-- service protocol for many unary ops
\end{code}
\newcommand\rstExampleManyUnaryp{%
\begin{code}
unaryp : Session n → Session n
unaryp s = ⁇ int ∙ ‼ int ∙ s

many-unaryp : Session 0
many-unaryp = μ & [ unaryp (` zero) , end ]
\end{code}}
\newcommand\rstExampleArithP{%
\begin{code}
arithp s = & [ binaryp s , unaryp s ]
\end{code}}
\begin{code}[hide]
arithp-raw : Session n → Session n
arithp-raw s = &′ {k = 2} (λ{ zero → binaryp s ; (suc zero) → unaryp s})


variable
  A A′ A″ A₁ A₂ : Set
  T t : Type
  S s s₁ s₂ : Session n
\end{code}
\newcommand\rstTypeInterpretation{%
\begin{code}
T⟦_⟧ : Type → Set
T⟦ int ⟧ = ℤ
T⟦ bool ⟧ = Bool
\end{code}}
\begin{code}[hide]
T⟦ nat ⟧ = ℕ
T⟦ fin k ⟧ = Fin k

module formatting2 where

\end{code}
\newcommand\rstBranchingCommand{%
\begin{code}
  -- data Cmd (A : Set) : Session n → Set where
  --   SELECT : ∀ {si} → (setl : A → Fin k × A)
  --                   → ((i : Fin k) → Cmd A (si i))
  --                   → Cmd A (⊕ si)
  --   CHOICE : ∀ {si} → (getl : Fin k → A → A)
  --                   → ((i : Fin k) → Cmd A (si i))
  --                   → Cmd A (& si)
\end{code}}
\newcommand\rstCommand{%
\begin{code}
data Cmd n (A : Set) : Session n → Set where
  LOOP     : Cmd (suc n) A s → Cmd n A (μ s)
  CONTINUE : (i : Fin n) → Cmd n A (` i)
\end{code}}
\begin{code}[hide]
  END    : Cmd n A end
  SEND   : (A → A × T⟦ T ⟧) → Cmd n A S → Cmd n A (‼ T ∙ S)
  RECV   : (T⟦ T ⟧ → A → A) → Cmd n A S → Cmd n A (⁇ T ∙ S)
  SELECT : ∀ {k si} → (i : Fin k) → Cmd n A (si i) → Cmd n A (⊕′ si)
  CHOICE : ∀ {k si} → (Fin k → A → A) → ((i : Fin k) → Cmd n A (si i)) → Cmd n A (&′ si)
\end{code}
\newcommand\rstAddpCommand{%
\begin{code}
addp-command : Cmd n ℤ s → Cmd n ℤ (binaryp s)
addp-command cmd = RECV (λ x a → x) $ RECV (λ y a → y + a) $ SEND (λ a → ⟨ a , a ⟩) $ cmd

\end{code}}
\newcommand\rstSumupCommand{%
\begin{code}
addup-command : Cmd n ℤ s → Cmd n ℤ (unaryp s)
addup-command cmd = RECV (λ x a → x + a) $ SEND (λ a → ⟨ a , a ⟩) $ cmd

sumup-command : Cmd 0 ℤ many-unaryp
sumup-command = LOOP $ CHOICE (λ _ a → a) λ where
  zero → addup-command (CONTINUE zero)
  (suc zero) → END
\end{code}}
\newcommand\rstPostulates{%
\begin{code}
postulate
  Channel : Set
  primAccept : IO Channel
  primClose  : Channel → IO ⊤
  primSend   : A → Channel → IO ⊤
  primRecv   : Channel → IO A
\end{code}}
\newcommand\rstCommandStore{%
\begin{code}
CmdStore : ∀ n → Set → Set
CmdStore n A = (i : Fin n) → ∃[ s ] (Cmd (suc (toℕ (opposite i))) A s)
\end{code}}
\newcommand\rstPops{%
\begin{code}
pop1 : ∀{n} → CmdStore (suc n) A → CmdStore n A
pop : CmdStore (suc n) A → (i : Fin (suc n)) → CmdStore (suc (toℕ (opposite i))) A
\end{code}}
\begin{code}[hide]
pop1 cms i with cms (suc i)
... | cms₁ rewrite toℕ-inject₁ (opposite i) = cms₁

pop {n} cms zero rewrite toℕ-fromℕ n = cms
pop {suc n} cms (suc i) = subst (λ H → CmdStore (suc H) _) (sym (toℕ-inject₁ (opposite i))) (pop (pop1 cms) i)
\end{code}
\begin{code}[hide]
module alternative-executor where
  exec : Cmd n A s → CmdStore n A → (init : A) → Channel
    → IO (∃[ n ] (CmdStore (suc n) A × A) ⊎ A)
  exec {n = n} {A = A} {s = μ s} (LOOP cmd) cms st ch = exec cmd cms′ st ch
    where cms′ : CmdStore (suc n) A
          cms′ zero    rewrite toℕ-fromℕ n = ⟨ s , cmd ⟩
          cms′ (suc i) rewrite toℕ-inject₁ (opposite i) = cms i
  exec {n = suc n} (CONTINUE i) cms st ch = pure (inj₁ ⟨ _ , ⟨ pop cms i , st ⟩ ⟩)
  exec END cms st ch = do
    primClose ch
    pure (inj₂ st)
  exec (SEND getx cmd) cms st ch = do
    let ⟨ st′ , x ⟩ = getx st
    primSend x ch
    exec cmd cms st′ ch
  exec (RECV putx cmd) cms st ch = do
    x ← primRecv ch
    let st′ = putx x st
    exec cmd cms st′ ch
  exec (SELECT i cmd) cms st ch = do
    primSend i ch
    exec cmd cms st ch
  exec (CHOICE putx f-cmd) cms st ch = do
    x ← primRecv ch
    let st′ = putx x st
    exec (f-cmd x) cms st′ ch
\end{code}
\newcommand\rstAlternativeExecutorRestart{%
\begin{code}
  CmdCont : Set → Set
  CmdCont A = ∃[ n ] (CmdStore (suc n) A × A)

  restart : CmdCont A → Channel → IO (CmdCont A ⊎ A)
  restart ⟨ n , ⟨ cms , st ⟩ ⟩ ch
    with cms zero
  ... | ⟨ s₀ , cmd₀ ⟩ rewrite toℕ-fromℕ n = exec cmd₀ cms st ch
\end{code}}
\newcommand\rstExecutorSignature{%
\begin{code}
Gas = ℕ
exec : Gas → Cmd n A s → CmdStore n A → (init : A) → Channel → IO A
\end{code}}
\begin{code}[hide]
exec k END cms state ch = do
  primClose ch
  pure state
exec k (SEND getx cmd) cms state ch = do
  let ⟨ state′ , x ⟩ = getx state
  primSend x ch
  exec k cmd cms state′ ch
exec k (RECV putx cmd) cms state ch = do
  x ← primRecv ch
  let state′ = putx x state
  exec k cmd cms state′ ch
exec k (SELECT i cmd) cms state ch = do
  primSend i ch
  exec k cmd cms state ch
exec k (CHOICE putx f-cmd) cms state ch = do
  x ← primRecv ch
  let state′ = putx x state
  exec k (f-cmd x) cms state′ ch
\end{code}
\newcommand\rstExecutor{%
\begin{code}
exec {n = n} {A = A} {s = μ s} k (LOOP cmd) cms state ch = exec k cmd cms′ state ch
  where cms′ : CmdStore (suc n) A
        cms′ zero    rewrite toℕ-fromℕ n = ⟨ s , cmd ⟩
        cms′ (suc i) rewrite toℕ-inject₁ (opposite i) = cms i
exec {suc n} {A} zero (CONTINUE i) cms state ch = pure state -- hack alert!
exec {suc n} {A} (suc k) (CONTINUE i) cms state ch
  with cms i
... | ⟨ s-i , cmd-i ⟩ = exec k cmd-i (pop cms i) state ch
\end{code}}
\newcommand\rstAcceptor{%
\begin{code}
record Accepting {n} A s : Set where
  constructor ACC
  field cmd : Cmd n A s

acceptor : {s : Session 0} → Gas → Accepting A s → A → IO A
acceptor k (ACC cmd) a = primAccept >>= exec k cmd (λ()) a
\end{code}}

