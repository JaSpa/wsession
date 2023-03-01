\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- required for IO -}
module ST-recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc; toℕ; opposite)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Integer using (ℤ; 0ℤ; _+_; -_; +_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)

open import Data.Unit using (⊤; tt)

open import Function.Base using (case_of_; _∘_; const; constᵣ; _$_; id)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; cong₂; trans; module ≡-Reasoning)

open import IO

open import Utils


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
    ⊕′ : (Si : (i : Fin k) → Session n) → Session n
    &′ : (Si : (i : Fin k) → Session n) → Session n
\end{code}}
\newcommand\rstSession{%
\begin{code}
data Session (n : ℕ) : Set where
  ‼_∙_ : Type → Session n → Session n
  ⁇_∙_ : Type → Session n → Session n
  end : Session n
  ⊕′ : (Si : (i : Fin k) → Session n) → Session n
  &′ : (Si : (i : Fin k) → Session n) → Session n
  μ_ : Session (suc n) → Session n
  `_ : Fin n → Session n
\end{code}}
\begin{code}[hide]

pattern recv t s = ⁇ t ∙ s
pattern send t s = ‼ t ∙ s

infixr 20 ‼_∙_ ⁇_∙_
infixr 20 μ_ `_

-- duality
dual : Session n → Session n
dual (send T S) = recv T (dual S)
dual (recv T S) = send T (dual S)
dual end = end
dual (⊕′ Si) = &′ (dual ∘ Si)
dual (&′ Si) = ⊕′ (dual ∘ Si)
dual (μ S) = μ (dual S)
dual (` x) = ` x


⊕ : Vec (Session n) k → Session n
⊕ = ⊕′ ∘ vec→fin

& : Vec (Session n) k → Session n
& = &′ ∘ vec→fin
  

-- service protocol for a binary function
binaryp : Session n → Session n
binaryp S = ⁇ int ∙ ⁇ int ∙ ‼ int ∙ S
-- service protocol for a unary function
-- service protocol for choosing between a binary and a unary function
arithp : Session n → Session n
-- service protocol for many unary ops
\end{code}
\newcommand\rstExampleManyUnaryp{%
\begin{code}
unaryp : Session n → Session n
unaryp S = ⁇ int ∙ ‼ int ∙ S

many-unaryp : Session 0
many-unaryp = μ & [ unaryp (` zero) , end ]
\end{code}}
\newcommand\rstExampleArithP{%
\begin{code}
arithp S = & [ binaryp S , unaryp S ]
\end{code}}
\begin{code}[hide]
arithp-raw : Session n → Session n
arithp-raw S = &′ {k = 2} (λ{ zero → binaryp S ; (suc zero) → unaryp S})


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
data Cmd (n : ℕ) (A : Set) : Session n → Set where
  LOOP     : Cmd (suc n) A S → Cmd n A (μ S)
  CONTINUE : (i : Fin n) → Cmd n A (` i)
\end{code}}
\newcommand\rstCommandUNROLL{%
\begin{code}
  UNROLL   : Cmd (suc n) A S → Cmd n A (μ S) → Cmd n A (μ S)
\end{code}}
\begin{code}[hide]
  CLOSE  : Cmd n A end
  SEND   : (A → A × T⟦ T ⟧) → Cmd n A S → Cmd n A (‼ T ∙ S)
  RECV   : (T⟦ T ⟧ → A → A) → Cmd n A S → Cmd n A (⁇ T ∙ S)
  SELECT : ∀ {Si} → (i : Fin k) → Cmd n A (Si i) → Cmd n A (⊕′ Si)
  CHOICE : ∀ {Si} → ((i : Fin k) → Cmd n A (Si i)) → Cmd n A (&′ Si)
\end{code}
\newcommand\rstAddpCommand{%
\begin{code}
addp-command : Cmd n ℤ S → Cmd n ℤ (binaryp S)
addp-command cmd = RECV (λ x a → x) $ RECV (λ y a → y + a) $ SEND (λ a → ⟨ a , a ⟩) $ cmd

\end{code}}
\newcommand\rstSumupCommand{%
\begin{code}
addup-command : Cmd n ℤ S → Cmd n ℤ (unaryp S)
addup-command cmd = RECV (λ x a → x + a) $ SEND (λ a → ⟨ a , a ⟩) $ cmd

runningsum-command : Cmd 0 ℤ many-unaryp
runningsum-command = LOOP $ CHOICE λ where
  zero → addup-command (CONTINUE zero)
  (suc zero) → CLOSE
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
CmdStore : ℕ → Set → Set
CmdStore n A = (i : Fin n) → ∃[ S ] (Cmd (toℕ (opposite i)) A S)
\end{code}}
\newcommand\rstPops{%
\begin{code}
push : CmdStore n A → Cmd n A S → CmdStore (suc n) A
pop1 : CmdStore (suc n) A → CmdStore n A
pop  : CmdStore (suc n) A → (i : Fin (suc n)) → CmdStore (suc (toℕ (opposite i))) A
\end{code}}
\begin{code}[hide]
push {n}{S = S} cms cmd zero    rewrite toℕ-fromℕ n = ⟨ S , cmd ⟩
push cms cmd (suc i) rewrite toℕ-inject₁ (opposite i) = cms i

pop1 cms i with cms (suc i)
... | cms₁ rewrite toℕ-inject₁ (opposite i) = cms₁

pop {n} cms zero rewrite toℕ-fromℕ n = cms
pop {suc n} cms (suc i) = subst (λ H → CmdStore (suc H) _) (sym (toℕ-inject₁ (opposite i))) (pop (pop1 cms) i)
\end{code}
\begin{code}[hide]
module alternative-executor where
  exec : Cmd n A S → CmdStore n A → (init : A) → Channel
    → IO (∃[ n ] (CmdStore (suc n) A × A) ⊎ A)
  exec (UNROLL body-cmd next-cmd) cms st ch = exec body-cmd (push cms next-cmd) st ch
  exec (LOOP cmd) cms st ch = exec cmd (push cms (LOOP cmd)) st ch
  exec {n = suc n} (CONTINUE i) cms st ch = pure (inj₁ ⟨ _ , ⟨ pop cms i , st ⟩ ⟩)
  exec CLOSE cms st ch = do
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
  exec (CHOICE f-cmd) cms st ch = do
    x ← primRecv ch
    exec (f-cmd x) cms st ch
\end{code}
\newcommand\rstAlternativeExecutorRestart{%
\begin{code}
  CmdCont : Set → Set
  CmdCont A = ∃[ n ] (CmdStore (suc n) A × A)

  restart : CmdCont A → Channel → IO (CmdCont A ⊎ A)
  restart ⟨ n , ⟨ cms , st ⟩ ⟩ ch
    with cms zero
  ... | ⟨ s₀ , cmd₀ ⟩ rewrite toℕ-fromℕ n = exec cmd₀ (pop1 cms) st ch
\end{code}}
\newcommand\rstExecutorSignature{%
\begin{code}
Gas = ℕ
exec : Gas → Cmd n A S → CmdStore n A → (init : A) → Channel → IO A
\end{code}}
\begin{code}[hide]
exec k CLOSE cms state ch = do
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
exec k (CHOICE f-cmd) cms state ch = do
  x ← primRecv ch
  exec k (f-cmd x) cms state ch
\end{code}
\newcommand\rstExecutor{%
\begin{code}
exec g (LOOP cmd) cms state ch = exec g cmd (push cms (LOOP cmd)) state ch
exec {suc n} {A} zero (CONTINUE i) cms state ch = pure state -- hack alert!
exec {suc n} {A} (suc g) (CONTINUE i) cms state ch
  with cms i
... | ⟨ _ , cmd-i ⟩ = exec g cmd-i (pop1 (pop cms i)) state ch
\end{code}}
\newcommand\rstExecutorUNROLL{%
\begin{code}
exec g (UNROLL body-cmd next-cmd) cms st ch = exec g body-cmd (push cms next-cmd) st ch
\end{code}}
\newcommand\rstAcceptor{%
\begin{code}
record Accepting {n} A S : Set where
  constructor ACC
  field cmd : Cmd n A S

acceptor : {S : Session 0} → Gas → Accepting A S → A → IO A
acceptor k (ACC cmd) a = primAccept >>= exec k cmd (λ()) a
\end{code}}
\newcommand\rstClientExample{%
\begin{code}
runningsum-client : Cmd 0 ⊤ (dual many-unaryp)
runningsum-client =
  UNROLL (SELECT zero $ SEND (λ x → ⟨ tt , + 17 ⟩) $ RECV constᵣ (CONTINUE zero)) $
  UNROLL (SELECT zero $ SEND (λ x → ⟨ tt , + 4 ⟩)  $ RECV constᵣ (CONTINUE zero)) $
  LOOP (SELECT (suc zero) CLOSE)
\end{code}}
