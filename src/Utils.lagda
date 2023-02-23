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

\end{code}
