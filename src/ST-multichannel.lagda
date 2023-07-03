\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- for IO -}
module ST-multichannel where
{-# FOREIGN GHC import qualified Control.Concurrent.UntypedChannel as UC #-}

open import Data.Bool using (Bool; true; false;if_then_else_)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Integer using (ℤ)
open import Data.Fin using (Fin; suc; zero; _≟_)
open import Data.Fin.Subset using (Subset)
open import Data.Product using (_×_; Σ; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; [] ; _∷_; lookup; remove; updateAt)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Function.Base using (case_of_; const)

open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

-- make the compiler happy

open import IO.Primitive

_>>_ : ∀ {a b} {A : Set a} {B : Set b} → IO A → IO B → IO B
ioa >> iob = ioa >>= λ a → iob

-- end compiler support

open import Types

variable
  m n o : ℕ
  f : Fin (suc n)
  A : Set
  B A′ A₁ A₂ : Set

-- splitting

data Split : ℕ → ℕ → Set where
  null : Split zero zero
  left : Split m n → Split (suc m) n
  right : Split m n → Split m (suc n)

apply-split : Split m n → Vec A (m + n) → Vec A m × Vec A n
apply-split null [] = ⟨ [] , [] ⟩
apply-split (left sp) (x ∷ v)
  with apply-split sp v
... | ⟨ vl , vr ⟩ = ⟨ x ∷ vl , vr ⟩
apply-split{m}{suc n} (right sp) v
  rewrite +-suc m n
  with v
... | x ∷ v
  with apply-split sp v
... | ⟨ vl , vr ⟩ = ⟨ vl , x ∷ vr ⟩

locate-split : Split m n → Fin (m + n) → Fin m ⊎ Fin n
locate-split (left sp) zero = inj₁ zero
locate-split (left sp) (suc f)
  with locate-split sp f
... | inj₁ x = inj₁ (suc x)
... | inj₂ y = inj₂ y
locate-split{m}{suc n} (right sp) f
  rewrite +-suc m n
  with f
... | zero = inj₂ zero
... | suc f
  with locate-split sp f
... | inj₁ x = inj₁ x
... | inj₂ y = inj₂ (suc y)

-- session types

\end{code}
\newcommand\multiSession{%
\begin{code}
data Direction : Set where
  INP OUT : Direction

data Session : Set where
  transmit : (d : Direction) → Type    →  Session → Session
  delegate : (d : Direction) → Session → Session → Session
  branch : (d : Direction) → Session → Session → Session
  end : Session
\end{code}}
\newcommand\multiMSesson{%
\begin{code}
data MSession : ℕ → Set
variable M M₁ M₂ : MSession n

Causality : Fin n → MSession n → MSession n → Set
CheckDual0 : MSession (suc m) → MSession (suc n) → Set

data MSession where
  transmit : (d : Direction) → (c : Fin n) → (T : Type) → MSession n → MSession n
  branch   : (d : Direction) → (c : Fin n) → (M₁ : MSession n) → (M₂ : MSession n)
    → Causality c M₁ M₂ → MSession n
  close : (c : Fin (suc n)) → MSession n → MSession (suc n)
  terminate : MSession zero
  connect : Split m n → (M₁ : MSession (suc m)) → (M₂ : MSession (suc n))
    → CheckDual0 M₁ M₂ → MSession (m + n)
  -- assume new channel has address zero in both threads
  delegateOUT : (c j : Fin (suc n)) → c ≢ j → Session → MSession n → MSession (suc n)
  delegateIN  : (c : Fin n) → MSession (suc n) → MSession n
  -- received channel has address zero in continuation
\end{code}}
\begin{code}[hide]

pattern select x s₁ s₂ p = branch OUT x s₁ s₂ p
pattern choice x s₁ s₂ p = branch INP x s₁ s₂ p

pattern recv x t s = transmit INP x t s
pattern send x t s = transmit OUT x t s

-- adjust index f if index x is removed from set

adjust : (f : Fin (suc n)) (x : Fin (suc n)) → f ≢ x → Fin n
adjust zero zero f≢x = ⊥-elim (f≢x refl)
adjust{suc n} zero (suc x) f≢x = zero
adjust{suc n} (suc f) zero f≢x = f
adjust{suc n} (suc f) (suc x) f≢x
  with adjust f x (λ{ refl → f≢x refl})
... | r = suc r

-- duality

dual-dir : Direction → Direction
dual-dir INP = OUT
dual-dir OUT = INP

dual : Session → Session
dual (branch d s₁ s₂) = branch (dual-dir d) (dual s₁) (dual s₂)
dual (transmit d t s) = transmit (dual-dir d) t (dual s)
dual (delegate d s₀ s) = delegate (dual-dir d) s₀ (dual s)
dual end = end

-- projection

\end{code}
\newcommand\multiProjection{%
\begin{code}
project : Fin n → MSession n → Session
project c (connect sp-c M₁ M₂ _) with locate-split sp-c c
... | inj₁ x = project (suc x) M₁
... | inj₂ y = project (suc y) M₂
project c (branch d x M₁ M₂ causal) with c ≟ x
... | no c≢x = project c M₁  -- we have (causal c c≢x : project c M₁ ≡ project c M₂)
... | yes refl = branch d (project c M₁) (project c M₂)
project c (transmit d x t M) with c ≟ x
... | no c≢x = project c M
... | yes refl = transmit d t (project c M)
project {suc n} c (close x M) with c ≟ x
... | no c≢x = project (adjust c x c≢x) M
... | yes refl = end
project c (delegateOUT x j x≢j sj M) with c ≟ x
... | yes refl = delegate OUT sj (project (adjust c j x≢j) M)
... | no c≢x with c ≟ j
... | yes refl = sj
... | no c≢j = project (adjust c j c≢j) M
project c (delegateIN x M) with c ≟ x
... | yes refl = delegate INP (project zero M) (project (suc c) M)
... | no c≢x = project (suc c) M

Causality {n} i M₁ M₂ = ∀ (j : Fin n) → j ≢ i → project j M₁ ≡ project j M₂
CheckDual0 M₁ M₂ = project zero M₁ ≡ dual (project zero M₂)
\end{code}}
\newcommand\multiCmd{%
\begin{code}
data Cmd (R A : Set) : (n : ℕ) → MSession n → Set₁ where
  CLOSE  : ∀ c → (A → B) → Cmd R B n M → Cmd R A (suc n) (close c M)
  SEND   : ∀ c → (A → ⟦ T ⟧ × B) → Cmd R B n M → Cmd R A n (send c T M)
  RECV   : ∀ c → (⟦ T ⟧ → A → B) → Cmd R B n M → Cmd R A n (recv c T M)
  SELECT : ∀ {F} c → (causal : Causality c M₁ M₂) → (A → Σ Bool F)
    → Cmd R (F true) n M₁ → Cmd R (F false) n M₂ → Cmd R A n (select c M₁ M₂ causal)
  CHOICE : ∀ c → (causal : Causality c M₁ M₂)
    → Cmd R A n M₁ → Cmd R A n M₂ → Cmd R A n (choice c M₁ M₂ causal)
  CONNECT : ∀ {M₁ : MSession (suc m)} {M₂ : MSession (suc n)} (check : CheckDual0 M₁ M₂)
    → (split : A → A₁ × A₂)
    → (sp : Split m n)
    → Cmd R A₁ (suc m) M₁ → Cmd R A₂ (suc n) M₂
    → Cmd R A (m + n) (connect sp M₁ M₂ check)
  SENDCH : ∀ {sj} → ∀ c j → (c≢j : c ≢ j)
    → Cmd R A n M → Cmd R A (suc n) (delegateOUT c j c≢j sj M)
  RECVCH : ∀ c → Cmd R A (suc n) M → Cmd R A n (delegateIN c M)
  END    : (A → R) → Cmd R A 0 terminate
\end{code}}
\begin{code}[hide]
postulate
  Channel  : Set
  primSend : Channel → A → IO ⊤
  primRecv : Channel → IO A
  primClose : Channel → IO ⊤
  primFork : IO ⊤ → IO ⊤

data Channel×Channel : Set where
  ⟨_,_⟩ : Channel → Channel → Channel×Channel
{-# COMPILE GHC Channel×Channel = data UC.CPair (UC.CPair) #-}

postulate
  newChan  : IO Channel×Channel
\end{code}
\begin{code}[hide]
{-# COMPILE GHC Channel = type UC.Channel #-}
{-# COMPILE GHC primSend = \ _ -> UC.primSend #-}
{-# COMPILE GHC primRecv = \ _ -> UC.primRecv #-}
{-# COMPILE GHC primClose = UC.primClose #-}
{-# COMPILE GHC primFork = UC.primFork #-}
{-# COMPILE GHC newChan = UC.newChan #-}
\end{code}
\begin{code}[hide]
variable R : Set
\end{code}
\newcommand\multiExecSignature{%
\begin{code}
exec : Cmd R A n M → A → Vec Channel n → IO R
\end{code}}
\begin{code}[hide]
exec (SENDCH c j f≢j cmd) state chns = do
  primSend (lookup chns c) (lookup chns j)
  exec cmd state (remove chns j)
exec (RECVCH c cmd) state chns = do
  ch ← primRecv (lookup chns c)
  exec cmd state (ch ∷ chns)
exec (CONNECT _ split split-ch cmds₁ cmds₂) state chns =
  let ⟨ state₁ , state₂ ⟩ = split state in
  let ⟨ chns₁ , chns₂ ⟩ = apply-split split-ch chns in
  newChan >>= λ{ ⟨ ch₁ , ch₂ ⟩ →
  primFork (exec cmds₁ state₁ (ch₁ ∷ chns₁) >> pure tt) >>
  exec cmds₂ state₂ (ch₂ ∷ chns₂) }
exec (CLOSE c gend cmd) state chns = do
  primClose (lookup chns c)
  exec cmd (gend state) (remove chns c)
exec (SEND c getx cmds) state chns =
  let ⟨ x , state′ ⟩ = getx state in
  primSend (lookup chns c) x >> exec cmds state′ chns
exec (RECV c putx cmds) state chns =
  primRecv (lookup chns c) >>= λ x →
  let state′ = putx x state in
  exec cmds state′ chns
exec (SELECT c _ getx cmds₁ cmds₂) state chns
  with getx state
... | ⟨ false , a ⟩ = do
  primSend (lookup chns c) false
  exec cmds₂ a chns
... | ⟨ true , a ⟩ = do
  primSend (lookup chns c) true
  exec cmds₁ a chns
exec (CHOICE c _ cmd₁ cmd₂) state chns = do
  b ← primRecv (lookup chns c)
  if b then exec cmd₁ state chns
       else exec cmd₂ state chns
exec (END f) state [] = do
  pure (f state)

runCmd : Cmd R A 0 M → A → IO R
runCmd cmd init = do
  exec cmd init []
\end{code}}
