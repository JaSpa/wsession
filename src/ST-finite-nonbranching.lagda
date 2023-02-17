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
  n k : ℕ
\end{code}
\newcommand\stFiniteType{%
\begin{code}
data Type : Set where
  int bool : Type
\end{code}}
\begin{code}[hide]
  nat : Type
  fin : ℕ → Type

module formatting1 where
\end{code}
\newcommand\stBranchingType{%
\begin{code}
  data Session : Set where
    ⊕ & : ∀ {k} → (si : (i : Fin k) → Session) → Session
\end{code}}
\newcommand\stFiniteSession{%
\begin{code}
data Session : Set where
  ‼_∙_ ⁇_∙_ : Type → Session → Session
  end : Session
\end{code}}
\begin{code}[hide]
  ⊕ & : ∀ {k} → (si : (i : Fin k) → Session) → Session
\end{code}
\begin{code}[hide]
  sel chc : ∀{k} → Vec Session k → Session
  select choice : Session → Session → Session

pattern recv t s = ⁇ t ∙ s
pattern send t s = ‼ t ∙ s

infixr 20 ‼_∙_ ⁇_∙_


vec→fin : Vec Session k → (Fin k → Session)
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
\end{code}
\newcommand\stTypeInterpretation{%
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
\newcommand\stBranchingCommand{%
\begin{code}
  data Command (A : Set) : Session → Set where
    SELECT : ∀ {si} → (setl : A → Fin k × A)
                    → ((i : Fin k) → Command A (si i))
                    → Command A (⊕ si)
    CHOICE : ∀ {si} → (getl : Fin k → A → A)
                    → ((i : Fin k) → Command A (si i))
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
  SELECT : ∀ {k si} → (A → Fin k × A) → ((i : Fin k) → Command A (si i)) → Command A (⊕ si)
  CHOICE : ∀ {k si} → (Fin k → A → A) → ((i : Fin k) → Command A (si i)) → Command A (& si)
\end{code}
\begin{code}[hide]
  SELECT2 : (A → Bool × A) → Command A s₁ → Command A s₂ → Command A (select s₁ s₂)
  CHOICE2 : (Bool → A → ⊤ × A) → Command A s₁ → Command A s₂ → Command A (choice s₁ s₂)

\end{code}
\newcommand\stAddpCommand{%
\begin{code}
addp-command : Command ℤ binaryp
addp-command = RECV (λ x a → x) $ RECV (λ y a → y + a) $ SEND (λ a → ⟨ a , a ⟩) $ END

negp-command : Command ℤ unaryp
negp-command = RECV (λ x a → - x) $ SEND (λ a → ⟨ a , a ⟩) $ END
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
  primClose  : Channel → IO ⊤
  primSend   : A → Channel → IO ⊤
  primRecv   : Channel → IO A
\end{code}}
\newcommand\stExecutorSignature{%
\begin{code}
exec : {s : Session} → Command A s → (init : A) → Channel → IO A
\end{code}}
\newcommand\stExecutor{%
\begin{code}
exec END state ch = do
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
exec (SELECT{n} getx cont) state ch = do
  let ⟨ x , state′ ⟩ = getx state
  primSend{Fin n} x ch
  exec (cont x) state′ ch

exec (CHOICE{n} putx cont) state ch = do
  x ← primRecv {Fin n} ch
  exec (cont x) state ch
\end{code}}
\begin{code}[hide]
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
record Accepting A s : Set where
  constructor ACC
  field cmd : Command A s

acceptor : Accepting A s → A → IO A
acceptor (ACC cmd) a = primAccept >>= exec cmd a
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

exec′ : {s : Session} → Command′ A A″ s → (init : A) → Channel → IO A″
exec′ END state ch = do
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
