\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- required for IO -}
module ST-finite-nonbranching where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; 0ℤ; _+_; -_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)

open import Data.Unit using (⊤; tt)

open import Function.Base using (case_of_; _∘_; const; _$_; id)

open import IO


pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []


variable
  n : ℕ
\end{code}
\newcommand\stFiniteType{%
\begin{code}
data Type : Set where
  nat int bool : Type
  fin : ℕ → Type
\end{code}}
\begin{code}[hide]
module formatting1 where
\end{code}
\newcommand\stBranchingType{%
\begin{code}
  data Session : Set where
    ⊕ & : ∀ {n} → (si : (i : Fin n) → Session) → Session
\end{code}}
\newcommand\stFiniteSession{%
\begin{code}
data Session : Set where
  ‼_∙_ ⁇_∙_ : Type → Session → Session
  end : Session
\end{code}}
\begin{code}[hide]
  ⊕ & : ∀ {n} → (si : (i : Fin n) → Session) → Session
\end{code}
\begin{code}[hide]
  sel chc : ∀{n} → Vec Session n → Session
  select choice : Session → Session → Session

pattern recv t s = ⁇ t ∙ s
pattern send t s = ‼ t ∙ s

infixr 20 ‼_∙_ ⁇_∙_


vec→fin : Vec Session n → (Fin n → Session)
vec→fin {zero} [] = λ()
vec→fin {suc n} (x ∷ v) = λ where
  zero → x
  (suc i) → vec→fin v i

⊕′ : Vec Session n → Session
⊕′ = ⊕ ∘ vec→fin

&′ : Vec Session n → Session
&′ = & ∘ vec→fin
  

-- service protocol for a binary function
binaryp : Session
-- service protocol for a unary function
unaryp : Session 
-- service protocol for choosing between a binary and a unary function
arithp : Session
\end{code}
\newcommand\stExampleBinpUnP{%
\begin{code}
binaryp = ⁇ int ∙ ⁇ int ∙ ‼ int ∙ end
unaryp = ⁇ int ∙ ‼ int ∙ end
\end{code}}
\newcommand\stExampleArithP{%
\begin{code}
arithp = &′ [ binaryp , unaryp ]
\end{code}}
\begin{code}[hide]
arithp-raw = & {2} (λ{ zero → binaryp ; (suc zero) → unaryp})

arithpv : Session
arithpv = chc (binaryp ∷ (unaryp ∷ []))

variable
  A A′ A″ A₁ A₂ : Set
  T t : Type
  S s s₁ s₂ : Session

T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ
T⟦ int ⟧ = ℤ
T⟦ bool ⟧ = Bool
T⟦ fin n ⟧ = Fin n

module formatting2 where

\end{code}
\newcommand\stBranchingCommand{%
\begin{code}
  data Command (A : Set) : Session → Set where
    SELECT : ∀ {si} → (setl : A → Fin n × A)
                    → ((i : Fin n) → Command A (si i))
                    → Command A (⊕ si)
    CHOICE : ∀ {si} → (getl : Fin n → A → A)
                    → ((i : Fin n) → Command A (si i))
                    → Command A (& si)
\end{code}}
\newcommand\stCommand{%
\begin{code}
data Command (A : Set) : Session → Set where
  END    : Command A end
  SEND   : (A → A × T⟦ T ⟧) → Command A S → Command A (‼ T ∙ S)
  RECV   : (T⟦ T ⟧ → A → A) → Command A S → Command A (⁇ T ∙ S)
\end{code}}
\begin{code}[hide]
  SELECT : ∀ {n si} → (A → Fin n × A) → ((i : Fin n) → Command A (si i)) → Command A (⊕ si)
  CHOICE : ∀ {n si} → (Fin n → A → A) → ((i : Fin n) → Command A (si i)) → Command A (& si)
\end{code}
\begin{code}[hide]
  SELECT2 : (A → Bool × A) → Command A s₁ → Command A s₂ → Command A (select s₁ s₂)
  CHOICE2 : (Bool → A → ⊤ × A) → Command A s₁ → Command A s₂ → Command A (choice s₁ s₂)

\end{code}
\newcommand\stAddpCommand{%
\begin{code}
addp-command : Command ℤ binaryp
addp-command = RECV (λ x a → x) $ RECV (λ y a → y + a) $ SEND (λ a → ⟨ 0ℤ , a ⟩) $ END

negp-command : Command ℤ unaryp
negp-command = RECV const $ SEND (λ a → ⟨ 0ℤ , - a ⟩) $ END
\end{code}}
\newcommand\stArithpCommand{%
\begin{code}
arithp-command : Command ℤ arithp
arithp-command = CHOICE (const id) λ where
  zero → addp-command
  (suc zero) → negp-command
\end{code}}
\newcommand\stPostulates{%
\begin{code}
postulate
  Channel : Set
  primAccept : IO Channel
  primClose : Channel → IO ⊤
  primSend : ∀ {T} → T⟦ T ⟧ → Channel → IO ⊤
  primRecv : ∀ {T} → Channel → IO T⟦ T ⟧
\end{code}}
\newcommand\stExecutorSignature{%
\begin{code}
executor : {s : Session} → Command A s → (init : A) → Channel → IO A
\end{code}}
\newcommand\stExecutor{%
\begin{code}
executor END state ch = do
  primClose ch
  pure state
executor (SEND getx cmd) state ch = do
  let ⟨ state′ , x ⟩ = getx state
  primSend x ch
  executor cmd state′ ch
executor (RECV putx cmd) state ch = do
  x ← primRecv ch
  let state′ = putx x state
  executor cmd state′ ch
\end{code}}
\newcommand\stBranchingExecutor{%
\begin{code}
executor (SELECT{n} getx cont) state ch = do
  let ⟨ x , state′ ⟩ = getx state
  primSend{fin n} x ch
  executor (cont x) state′ ch

executor (CHOICE{n} putx cont) state ch = do
  x ← primRecv {fin n} ch
  executor (cont x) state ch
\end{code}}
\begin{code}[hide]
executor (SELECT2 getx cmd₁ cmd₂) state ch = do
  let ⟨ x , state′ ⟩ = getx state
  primSend {bool} x ch
  (case x of (λ{ false → executor cmd₁ state′ ch ; true → executor cmd₂ state′ ch}))
executor (CHOICE2 putx cmd₁ cmd₂) state ch = do
  x ← primRecv {bool} ch
  let ⟨ _ , state′ ⟩ = putx x state
  (case x of (λ{ false → executor cmd₁ state′ ch ; true → executor cmd₂ state′ ch}))
\end{code}
\newcommand\stAcceptor{%
\begin{code}
record Accepting A s : Set where
  constructor ACC
  field cmd : Command A s

acceptor : Accepting A s → A → IO A
acceptor (ACC cmd) a = primAccept >>= executor cmd a
\end{code}}
\begin{code}[hide]
----------------------------------------------------------------------
-- a Σ type isomorphic to A₁ ⊎ A₂

ifb : Set → Set → Bool → Set
ifb A₁ A₂ false = A₁
ifb A₁ A₂ true = A₂

zzfalse : Σ _ (ifb Bool ℕ)
zzfalse = ⟨ false , false ⟩

zztrue :  Σ _ (ifb Bool ℕ)
zztrue =  ⟨ true , 42 ⟩

fffun  : (x : Bool) → ifb Bool ℕ x
fffun false = false
fffun true = 42

ΣB : Set → Set → Set
ΣB A₁ A₂ = Σ _ (ifb A₁ A₂)


data Command′ (A : Set) : Set → Session → Set₁ where
  END    : Command′ A A end
  SEND   : (A → T⟦ t ⟧ × A′) → Command′ A′ A″ s → Command′ A A″ (send t s)
  RECV   : (T⟦ t ⟧ → A → A′) → Command′ A′ A″ s → Command′ A A″ (recv t s)
  SELECT21 : (A → A₁ ⊎ A₂) → Command′ A₁ A″ s₁ → Command′ A₂ A″ s₂ → Command′ A A″ (select s₁ s₂)
  CHOICE21 : ((x : Bool) → A → (case x of λ{false → A₁; true → A₂})) → Command′ A₁ A″ s₁ → Command′ A₂ A″ s₂ → Command′ A A″ (choice s₁ s₂)

  SELECT22 : (A → ΣB A₁ A₂) → Command′ A₁ A″ s₁ → Command′ A₂ A″ s₂ → Command′ A A″ (select s₁ s₂)

executor′ : {s : Session} → Command′ A A″ s → (init : A) → Channel → IO A″
executor′ END state ch = do
  primClose ch
  pure state
executor′ (SEND getx cmd) state ch = do
  let ⟨ x , state′ ⟩ = getx state
  primSend x ch
  executor′ cmd state′ ch
executor′ (RECV putx cmd) state ch = do
  x ← primRecv ch
  let state′ = putx x state
  executor′ cmd state′ ch
executor′ (SELECT21 getx cmd₁ cmd₂) state ch
  with getx state
... | inj₁ state₁ = do
      primSend {bool} true ch
      executor′ cmd₁ state₁ ch
... | inj₂ state₂ = do
      primSend {bool} false ch
      executor′ cmd₂ state₂ ch
executor′ (CHOICE21 putx cmd₁ cmd₂) state ch = do
  false ← primRecv {bool} ch
    where
      true → do
        let state′ = putx true state
        executor′ cmd₂ state′ ch
  let state′ = putx false state
  executor′ cmd₁ state′ ch
executor′ (SELECT22 getx cmd₁ cmd₂) state ch = do
  let bst = getx state
  primSend {bool} (proj₁ bst) ch
  ⟨ false , state₁ ⟩ ← pure bst
    where
      ⟨ true , state₂ ⟩ → executor′ cmd₂ state₂ ch
  executor′ cmd₁ state₁ ch

\end{code}
