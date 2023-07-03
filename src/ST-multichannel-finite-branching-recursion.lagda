\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- for IO -}
module ST-multichannel-finite-branching-recursion where
{-# FOREIGN GHC import qualified Control.Concurrent.UntypedChannel as UC #-}

open import Data.Bool using (Bool; true; false;if_then_else_)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Integer using (ℤ)
open import Data.Fin using (Fin; suc; zero; _≟_; toℕ; opposite)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Fin.Subset using (Subset)
open import Data.Product using (_×_; Σ; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; [] ; _∷_; lookup; remove; updateAt)
open import Data.List using (List; []; _∷_)

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
  k m n o : ℕ
  f : Fin (suc n)
  A : Set

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

data Session (y : ℕ) : Set where
  transmit : (d : Direction) → Type    →  Session y → Session y
  delegate : (d : Direction) → Session y → Session y → Session y
  branch : (d : Direction) → Session y → Session y → Session y
  mbranch : (d : Direction) → (Fin k → Session y) → Session y
  μ_ : Session (suc y) → Session y
  `_ : Fin y → Session y
  end : Session y
\end{code}}
\newcommand\multiMSesson{%
\begin{code}
data MSession {y} (Y : Vec ℕ y) : ℕ → Set
variable y : ℕ
variable Y : Vec ℕ y
variable M M₁ M₂ : MSession Y n

Causality : Fin n → MSession Y n → MSession Y n → Set
Causality* : Fin n → ∀ k → ((i : Fin k) → MSession Y n) → Set
CheckDual0 : MSession Y (suc m) → MSession Y (suc n) → Set

data MSession {y} Y where
  transmit : (d : Direction) → (c : Fin n) → (T : Type) → MSession Y n → MSession Y n
  branch   : (d : Direction) → (c : Fin n) → (M₁ : MSession Y n) → (M₂ : MSession Y n)
    → Causality c M₁ M₂ → MSession Y n
  mbranch  : (d : Direction) → (c : Fin n)
    → (Mᵢ : (i : Fin (suc k)) → MSession Y n)
    → Causality* c (suc k) Mᵢ → MSession Y n
  close : (c : Fin (suc n)) → MSession Y n → MSession Y (suc n)
  terminate : MSession Y zero
  connect : Split m n → (M₁ : MSession Y (suc m)) → (M₂ : MSession Y (suc n))
    → CheckDual0 M₁ M₂ → MSession Y (m + n)
  -- assume new channel has address zero in both threads
  delegateOUT : (c j : Fin (suc n)) → c ≢ j → Session y → MSession Y n → MSession Y (suc n)
  delegateIN  : (c : Fin n) → MSession Y (suc n) → MSession Y n
  -- received channel has address zero in continuation
  rec : MSession (n ∷ Y) n → MSession Y n
  var : (i : Fin y) → MSession Y (lookup Y i)
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

dual : ∀ {y} → Session y → Session y
dual (branch d s₁ s₂) = branch (dual-dir d) (dual s₁) (dual s₂)
dual (mbranch d sᵢ) = mbranch (dual-dir d) λ i → dual (sᵢ i)
dual (transmit d t s) = transmit (dual-dir d) t (dual s)
dual (delegate d s₀ s) = delegate (dual-dir d) s₀ (dual s)
dual (μ s) = μ (dual s)
dual (` i) = ` i
dual end = end


-- projection


\end{code}
\newcommand\multiProjection{%
\begin{code}
project : ∀ {y}{Y : Vec ℕ y} → Fin n → MSession Y n → Session y
project c (connect sp-c M₁ M₂ _) with locate-split sp-c c
... | inj₁ x = project (suc x) M₁
... | inj₂ y = project (suc y) M₂
project c (branch d x M₁ M₂ causal) with c ≟ x
... | no c≢x = project c M₁  -- we have (causal c c≢x : project c M₁ ≡ project c M₂)
... | yes refl = branch d (project c M₁) (project c M₂)
project c (mbranch d x Mᵢ causal*) with c ≟ x
... | no c≢x = project c (Mᵢ zero)
... | yes refl = mbranch d (λ i → project c (Mᵢ i))
project c (transmit d x t M) with c ≟ x
... | no c≢x = project c M
... | yes refl = transmit d t (project c M)
project {suc n} c (close x M) with c ≟ x
... | no c≢x = project (adjust c x c≢x) M
... | yes refl = end
project c (delegateOUT x j x≢j sj M) with c ≟ x
... | yes refl = delegate OUT sj (project (adjust c j x≢j) M)
... | no c≢x with c ≟ j
... | yes refl = sj -- sj
... | no c≢j = project (adjust c j c≢j) M
project c (delegateIN x M) with c ≟ x
... | yes refl = delegate INP (project zero M) (project (suc c) M)
... | no c≢x = project (suc c) M
project c (rec M) = μ (project c M)
project c (var i) = ` i

Causality {n} i M₁ M₂ = ∀ (j : Fin n) → j ≢ i → project j M₁ ≡ project j M₂
Causality* {n} i zero Mᵢ = ⊤
Causality* {n} i (suc k) Mᵢ = ∀ (j : Fin n) → j ≢ i → ∀ (h : Fin k) → project j (Mᵢ zero) ≡ project j (Mᵢ (suc h)) 
CheckDual0 M₁ M₂ = project zero M₁ ≡ dual (project zero M₂)
\end{code}}
\begin{code}[hide]

variable
  B A′ A₁ A₂ R : Set
  V : Vec Set y

\end{code}
-- R - final result type
-- y - number of open recs
-- A - argument type
-- V - vector of open argument types
-- n - number of channels
-- Y - vector of numbers of channels
\newcommand\multiCmd{%
\begin{code}
data Cmd {y : ℕ} (R : Set) : (A : Set) (V : Vec Set y) (n : ℕ) (Y : Vec ℕ y) → MSession Y n → Set₁ where
  CLOSE  : ∀ c → (A → B) → Cmd R B V n Y M → Cmd R A V (suc n) Y (close c M)
  SEND   : ∀ c → (A → ⟦ T ⟧ × B) → Cmd R B V n Y M → Cmd R A V n Y (send c T M)
  RECV   : ∀ c → (⟦ T ⟧ → A → B) → Cmd R B V n Y M → Cmd R A V n Y (recv c T M)
  SELECT : ∀ {F} c → (causal : Causality c M₁ M₂) → (A → Σ Bool F)
    → Cmd R (F true) V n Y M₁ → Cmd R (F false) V n Y M₂ → Cmd R A V n Y (select c M₁ M₂ causal)
  CHOICE : ∀ c → (causal : Causality c M₁ M₂)
    → Cmd R A V n Y M₁ → Cmd R A V n Y M₂ → Cmd R A V n Y (choice c M₁ M₂ causal)
  MSELECT : ∀ {F Mᵢ} c → (causal : Causality* c (suc k) Mᵢ) → (A → Σ (Fin (suc k)) F)
    → ((i : Fin (suc k)) → Cmd R (F i) V n Y (Mᵢ i))
    → Cmd R A V n Y (mbranch OUT c Mᵢ causal)
  MCHOICE : ∀ {Mᵢ} c → (causal : Causality* c (suc k) Mᵢ)
    → ((i : Fin (suc k)) → Cmd R A V n Y (Mᵢ i))
    → Cmd R A V n Y (mbranch INP c Mᵢ causal)
  CONNECT : ∀ {M₁ : MSession Y (suc m)} {M₂ : MSession Y (suc n)} (check : CheckDual0 M₁ M₂)
    → (split : A → A₁ × A₂)
    → (sp : Split m n)
    → Cmd R A₁ V (suc m) Y M₁ → Cmd R A₂ V (suc n) Y M₂
    → Cmd R A V (m + n) Y (connect sp M₁ M₂ check)
  SENDCH : ∀ {sj} → ∀ c j → (c≢j : c ≢ j)
    → Cmd R A V n Y M → Cmd R A V (suc n) Y (delegateOUT c j c≢j sj M)
  RECVCH : ∀ c → Cmd R A V (suc n) Y M → Cmd R A V n Y (delegateIN c M)
  END    : (A → R) → Cmd R A V 0 Y terminate

  LOOP   : Cmd R A (A ∷ V) n (n ∷ Y) M → Cmd R A V n Y (rec M)
  CONTINUE : (i : Fin y) → Cmd R (lookup V i) V (lookup Y i) Y (var i)
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
\begin{code}
shrink : ∀ {n}{a}{A : Set a} → Vec A n → (i : Fin n) → Vec A (suc (toℕ (opposite i)))
shrink {n} V zero rewrite toℕ-fromℕ n = V
shrink {suc n} (x ∷ V) (suc i) rewrite toℕ-inject₁ (opposite i) = shrink V i

-- y - number of recursion variables
-- R - return type
-- V - vector of input types
CmdStore : ∀ y → (R : Set) (V : Vec Set y) (Y : Vec ℕ y) → Set₁
CmdStore y R V Y = (i : Fin y)
  → Σ (MSession (shrink Y i) (lookup Y i))
      (Cmd{suc (toℕ (opposite i))} R (lookup V i) (shrink V i) (lookup Y i) (shrink Y i))

push : CmdStore y R V Y
  → Cmd R A (A ∷ V) n (n ∷ Y) M → CmdStore (suc y) R (A ∷ V) (n ∷ Y)
push {y = y}{M = M} cms cmd zero rewrite toℕ-fromℕ y = ⟨ M , cmd ⟩
push cms cmd (suc i) rewrite toℕ-inject₁ (opposite i) = cms i

pop1 : CmdStore (suc y) R (A ∷ V) (n ∷ Y) → CmdStore y R V Y
pop1 cms i
  with cms (suc i)
... | cmsᵢ  rewrite toℕ-inject₁ (opposite i) = cmsᵢ

pop : CmdStore (suc y) R V Y → (i : Fin (suc y)) → CmdStore (suc (toℕ (opposite i))) R (shrink V i) (shrink Y i)
pop {y = y} cms zero rewrite toℕ-fromℕ y = cms
pop {y = suc y} {V = A ∷ V}{Y = n ∷ Y} cms (suc i)
  rewrite toℕ-inject₁ (opposite i) = pop (pop1 cms) i


\end{code}
\newcommand\multiExec{%
\begin{code}
{-# TERMINATING #-} -- a lie
exec : Cmd R A V n Y M → CmdStore y R V Y → A → Vec Channel n → IO R
exec (SENDCH c j f≢j cmd) cms state chns = do
  primSend (lookup chns c) (lookup chns j)
  exec cmd cms state (remove chns j)
exec (RECVCH c cmd) cms state chns = do
  ch ← primRecv (lookup chns c)
  exec cmd cms state (ch ∷ chns)
exec (CONNECT _ split split-ch cmds₁ cmds₂) cms state chns =
  let ⟨ state₁ , state₂ ⟩ = split state in
  let ⟨ chns₁ , chns₂ ⟩ = apply-split split-ch chns in
  newChan >>= λ{ ⟨ ch₁ , ch₂ ⟩ →
  primFork (exec cmds₁ cms state₁ (ch₁ ∷ chns₁) >> pure tt) >>
  exec cmds₂ cms state₂ (ch₂ ∷ chns₂) }
exec (CLOSE c gend cmd) cms state chns = do
  primClose (lookup chns c)
  exec cmd cms (gend state) (remove chns c)
exec (SEND c getx cmds) cms state chns =
  let ⟨ x , state′ ⟩ = getx state in
  primSend (lookup chns c) x >> exec cmds cms state′ chns
exec (RECV c putx cmds) cms state chns =
  primRecv (lookup chns c) >>= λ x →
  let state′ = putx x state in
  exec cmds cms state′ chns
exec (SELECT c _ getx cmds₁ cmds₂) cms state chns
  with getx state
... | ⟨ false , a ⟩ = do
  primSend (lookup chns c) false
  exec cmds₂ cms a chns
... | ⟨ true , a ⟩ = do
  primSend (lookup chns c) true
  exec cmds₁ cms a chns
exec (CHOICE c _ cmd₁ cmd₂) cms state chns = do
  b ← primRecv (lookup chns c)
  if b then exec cmd₁ cms state chns
       else exec cmd₂ cms state chns
exec (MSELECT c _ getx cmdsᵢ) cms state chns
  with getx state
... | ⟨ i , a ⟩ = do
  primSend (lookup chns c) i
  exec (cmdsᵢ i) cms a chns
exec (MCHOICE c _ cmdsᵢ) cms state chns = do
  i ← primRecv (lookup chns c)
  exec (cmdsᵢ i) cms state chns
exec (END f) cms state [] = do
  pure (f state)

exec (LOOP cmd) cms state chns = exec cmd (push cms cmd) state chns
exec{R}{y = suc y} (CONTINUE i) cms state chns
  with cms i
... | ⟨ Mᵢ , cmdᵢ ⟩ = exec cmdᵢ (pop cms i) state chns

runCmd : Cmd R A [] 0 [] M → A → IO R
runCmd cmd init = do
  exec cmd (λ()) init []
\end{code}}
