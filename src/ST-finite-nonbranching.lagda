\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- required for IO -}
module ST-finite-nonbranching where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; 0ℤ; _+_; -_; _≤ᵇ_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; proj₁; proj₂; <_,_>) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; map)

open import Data.Unit using (⊤; tt)

open import Function.Base using (case_of_; _∘_; const; _$_; id)

open import IO

open import Utils
open import Types
open import Channels IO ⊤

variable
  n k : ℕ
\end{code}
\begin{code}[hide]

module formatting1 where

\end{code}
\newcommand\stBranchingType{%
\begin{code}
  data Session : Set where
    ⊕′ : (Fin k → Session) → Session
    &′ : (Fin k → Session) → Session
\end{code}}
\newcommand\stFiniteSession{%
\begin{code}
data Session : Set where
  ‼_∙_ : Type → Session → Session
  ⁇_∙_ : Type → Session → Session
  end : Session
\end{code}}
\begin{code}[hide]
  ⊕′ : (Fin k → Session) → Session
  &′ : (Fin k → Session) → Session
\end{code}
\begin{code}[hide]
  sel chc : Vec Session k → Session
  select choice : Session → Session → Session

pattern recv t s = ⁇ t ∙ s
pattern send t s = ‼ t ∙ s

infixr 20 ‼_∙_ ⁇_∙_

⊕ : Vec Session n → Session
⊕ = ⊕′ ∘ vec→fin

& : Vec Session n → Session
& = &′ ∘ vec→fin

-- service protocol for a binary function
binaryp : Session
-- service protocol for a unary function
unaryp : Session 
-- service protocol for choosing between a binary and a unary function
arithp : Session
\end{code}
\begin{code}[hide]
{-# TERMINATING #-}
\end{code}
\newcommand\stDuality{%
\begin{code}
dual : Session → Session
dual (‼ T ∙ S) = ⁇ T ∙ dual S
dual (⁇ T ∙ S) = ‼ T ∙ dual S
dual end = end
\end{code}}
\begin{code}[hide]
dual (⊕′ f) = &′ (dual ∘ f)
dual (&′ f) = ⊕′ (dual ∘ f)
dual (sel v) = chc (map dual v)
dual (chc v) = sel (map dual v)
dual (select S S₁) = choice (dual S) (dual S₁)
dual (choice S S₁) = select (dual S) (dual S₁)
\end{code}
\newcommand\stExampleBinpUnP{%
\begin{code}
binaryp = ⁇ int ∙ ⁇ int ∙ ‼ int ∙ end
unaryp = ⁇ int ∙ ‼ int ∙ end
\end{code}}
\newcommand\stExampleArithP{%
\begin{code}
arithp = & [ binaryp , unaryp ]
\end{code}}
\begin{code}[hide]
arithp-raw = &′ {2} (λ{ zero → binaryp ; (suc zero) → unaryp})

arithpv : Session
arithpv = chc (binaryp ∷ (unaryp ∷ []))

variable
  A A′ A″ A₁ A₂ : Set
  S s s₁ s₂ : Session

module formatting2 where

\end{code}
\newcommand\stBranchingCommand{%
\begin{code}
  data Cmd (A : Set) : Session → Set where
    SELECT : ∀ {Sᵢ} → (i : Fin k) → Cmd A (Sᵢ i) → Cmd A (⊕′ Sᵢ)
    CHOICE : ∀ {Sᵢ} → ((i : Fin k) → Cmd A (Sᵢ i)) → Cmd A (&′ Sᵢ)
\end{code}}
\newcommand\stCommand{%
\begin{code}
data Cmd (A : Set) : Session → Set where
  CLOSE  : Cmd A end
  SEND   : (A → A × ⟦ T ⟧) → Cmd A S → Cmd A (‼ T ∙ S)
  RECV   : (⟦ T ⟧ → A → A) → Cmd A S → Cmd A (⁇ T ∙ S)
\end{code}}
\begin{code}[hide]
  SELECT : ∀ {Si} → (i : Fin k) → Cmd A (Si i) → Cmd A (⊕′ Si)
  CHOICE : ∀ {Si} → ((i : Fin k) → Cmd A (Si i)) → Cmd A (&′ Si)
\end{code}
\begin{code}[hide]
  SELECT2 : (A → Bool × A) → Cmd A s₁ → Cmd A s₂ → Cmd A (select s₁ s₂)
  CHOICE2 : (Bool → A → ⊤ × A) → Cmd A s₁ → Cmd A s₂ → Cmd A (choice s₁ s₂)
\end{code}
\newcommand\stDynamicBranchingCommand{%
\begin{code}
  DSELECT : ∀ {Sᵢ} → (getl : A → A × Fin k)
                   → ((i : Fin k) → Cmd A (Sᵢ i))
                   → Cmd A (⊕′ Sᵢ)
\end{code}}
\newcommand\stAddpCommand{%
\begin{code}
addp-command : Cmd ℤ binaryp
addp-command = RECV (λ x a → x) $ RECV (λ y a → y + a) $ SEND (λ a → ⟨ a , a ⟩) $ CLOSE
\end{code}}
\newcommand\stAddpCommandAlternative{%
\begin{code}
addp-command′ : Cmd ℤ binaryp
addp-command′ = RECV const $ RECV _+_ $ SEND < id , id > $ CLOSE
\end{code}}
\newcommand\stNegpCommand{%
\begin{code}
negp-command : Cmd ℤ (⁇ int ∙ ‼ int ∙ end)
negp-command = RECV (λ x a → - x) $ SEND (λ a → ⟨ a , a ⟩) $ CLOSE
\end{code}}
\newcommand\stNegpCommandAlternative{%
\begin{code}
negp-command′ : Cmd ℤ (⁇ int ∙ ‼ int ∙ end)
negp-command′ = RECV const $ SEND (λ a → ⟨ a , - a ⟩) $ CLOSE
\end{code}}
\newcommand\stArithpCommand{%
\begin{code}
arithp-command : Cmd ℤ arithp
arithp-command = CHOICE λ where
  zero → addp-command
  (suc zero) → negp-command
\end{code}}
\newcommand\stArithpClient{%
\begin{code}
Bool→F2 : Bool → Fin 2
Bool→F2 false = zero
Bool→F2 true = suc zero

arithp-client : Cmd ℤ (dual arithp)
arithp-client = DSELECT (λ z → ⟨ z , Bool→F2 (z ≤ᵇ 0ℤ) ⟩) λ where
  zero → SEND (λ z → ⟨ z , z ⟩) (SEND (λ z → ⟨ z , z ⟩) (RECV const CLOSE))
  (suc zero) → SEND (λ z → ⟨ z , z ⟩) (RECV const CLOSE)
\end{code}}
\newcommand\stExecutorSignature{%
\begin{code}
exec : Cmd A S → A → Channel → IO A
\end{code}}
\newcommand\stExecutor{%
\begin{code}
exec CLOSE state ch = do
  primClose ch
  pure state
exec (SEND getx cmd) state ch = do
  let ⟨ state′ , x ⟩ = getx state
  primSend x ch
  exec cmd state′ ch
exec (RECV putx cmd) state ch = do
  x ← primRecv ch
  let state′ = putx x state
  exec cmd state′ ch
\end{code}}
\newcommand\stBranchingExecutor{%
\begin{code}
exec (SELECT i cmd) state ch = do
  primSend i ch
  exec cmd state ch

exec (CHOICE cont) state ch = do
  x ← primRecv ch
  exec (cont x) state ch
\end{code}}
\begin{code}[hide]
exec (DSELECT getx cont) state ch = do
  let ⟨ state′ , i ⟩ = getx state
  primSend i ch
  exec (cont i) state′ ch

exec (SELECT2 getx cmd₁ cmd₂) state ch = do
  let ⟨ x , state′ ⟩ = getx state
  primSend {Bool} x ch
  (case x of (λ{ false → exec cmd₁ state′ ch ; true → exec cmd₂ state′ ch}))
exec (CHOICE2 putx cmd₁ cmd₂) state ch = do
  x ← primRecv {Bool} ch
  let ⟨ _ , state′ ⟩ = putx x state
  (case x of (λ{ false → exec cmd₁ state′ ch ; true → exec cmd₂ state′ ch}))
\end{code}
\newcommand\stAcceptor{%
\begin{code}
runServer : Cmd A S → A → IO A
runServer cmd a = primAccept >>= exec cmd a
\end{code}}
\newcommand\stAcceptorOld{%
\begin{code}
record Accepting A S : Set where
  constructor ACC
  field cmd : Cmd A S

acceptor : Accepting A S → A → IO A
acceptor (ACC cmd) a = primAccept >>= exec cmd a
\end{code}}
\newcommand\stCombinators{%
\begin{code}
XCmd : Set → Session → Set₁
XCmd A s = A → Channel → IO A

xclose : XCmd A end
xclose state ch = do
  primClose ch
  pure state

xsend : (A → A × ⟦ T ⟧) → XCmd A S → XCmd A (‼ T ∙ S)
xsend f xcmd = λ state ch → do
  let ⟨ state′ , x ⟩ = f state
  primSend x ch
  xcmd state′ ch
\end{code}}
\begin{code}[hide]
xrecv : (⟦ T ⟧ → A → A) → XCmd A S → XCmd A (⁇ T ∙ S)
xrecv f xcmd = λ state ch → do
  x ← primRecv ch
  let state′ = f x state
  xcmd state′ ch 

xselect : ∀ {Si} → (i : Fin k) → XCmd A (Si i) → XCmd A (⊕′ Si)
xselect i xcmd = λ state ch → do
  primSend i ch
  xcmd state ch

xchoice : ∀ {Si} → ((i : Fin k) → XCmd A (Si i)) → XCmd A (&′ Si)
xchoice f-xcont = λ state ch → do
  x ← primRecv ch
  f-xcont x state ch
\end{code}
\begin{code}[hide]
----------------------------------------------------------------------
-- a Σ type isomorphic to A₁ ⊎ A₂

ifb : ∀{ℓ}{A : Set ℓ} → A → A → Bool → A
ifb A₁ A₂ false = A₁
ifb A₁ A₂ true = A₂

ΣB : Set → Set → Set
ΣB A₁ A₂ = Σ _ (ifb A₁ A₂)

data Cmd′ (A : Set) : Set → Session → Set₁ where
  CLOSE  : Cmd′ A A end
  SEND   : (A → ⟦ T ⟧ × A′) → Cmd′ A′ A″ S → Cmd′ A A″ (send T S)
  RECV   : (⟦ T ⟧ → A → A′) → Cmd′ A′ A″ S → Cmd′ A A″ (recv T S)
  SELECT21 : (A → A₁ ⊎ A₂) → Cmd′ A₁ A″ s₁ → Cmd′ A₂ A″ s₂ → Cmd′ A A″ (select s₁ s₂)
  CHOICE21 : ((x : Bool) → A → (case x of λ{false → A₁; true → A₂})) → Cmd′ A₁ A″ s₁ → Cmd′ A₂ A″ s₂ → Cmd′ A A″ (choice s₁ s₂)

  SELECT22 : (A → ΣB A₁ A₂) → Cmd′ A₁ A″ s₁ → Cmd′ A₂ A″ s₂ → Cmd′ A A″ (select s₁ s₂)

exec′ : {s : Session} → Cmd′ A A″ s → (init : A) → Channel → IO A″
exec′ CLOSE state ch = do
  primClose ch
  pure state
exec′ (SEND getx cmd) state ch = do
  let ⟨ x , state′ ⟩ = getx state
  primSend x ch
  exec′ cmd state′ ch
exec′ (RECV putx cmd) state ch = do
  x ← primRecv ch
  let state′ = putx x state
  exec′ cmd state′ ch
exec′ (SELECT21 getx cmd₁ cmd₂) state ch
  with getx state
... | inj₁ state₁ = do
      primSend {Bool} true ch
      exec′ cmd₁ state₁ ch
... | inj₂ state₂ = do
      primSend {Bool} false ch
      exec′ cmd₂ state₂ ch
exec′ (CHOICE21 putx cmd₁ cmd₂) state ch = do
  false ← primRecv {Bool} ch
    where
      true → do
        let state′ = putx true state
        exec′ cmd₂ state′ ch
  let state′ = putx false state
  exec′ cmd₁ state′ ch
exec′ (SELECT22 getx cmd₁ cmd₂) state ch = do
  let bst = getx state
  primSend {Bool} (proj₁ bst) ch
  ⟨ false , state₁ ⟩ ← pure bst
    where
      ⟨ true , state₂ ⟩ → exec′ cmd₂ state₂ ch
  exec′ cmd₁ state₁ ch

\end{code}
