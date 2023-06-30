\begin{code}[hide]
module Utils where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)

open import Function using (_∘_)

vec→fin : ∀{ℓ}{A : Set ℓ}{k} → Vec A k → (Fin k → A)
vec→fin {k = zero}  []      = λ()
vec→fin {k = suc n} (x ∷ v) = λ where
  zero → x
  (suc i) → vec→fin v i

fin→vec : ∀{ℓ}{A : Set ℓ}{k} → (Fin k → A) → Vec A k
fin→vec {k = zero}  f = []
fin→vec {k = suc k} f = f zero ∷ fin→vec (f ∘ suc)



pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []

-- folklore trick for n-ary lists by Guillaume Allais

-- open import Data.Product using (_×_; _,_)
-- open import Data.List hiding ([_])

-- infixr 20 [_]

-- _^_ : ∀ {ℓ} → Set ℓ → ℕ → Set ℓ
-- A ^ zero  = A
-- A ^ suc n = A × (A ^ n)

-- [_] : ∀ {ℓ}{A : Set ℓ}{n : ℕ} → A ^ n → List A
-- [_] {n = zero}  x        = x ∷ []
-- [_] {n = suc n} (x , xs) = x ∷ [ xs ]

\end{code}
