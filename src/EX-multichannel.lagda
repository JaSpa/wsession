\begin{code}[hide]
{-# OPTIONS --guardedness #-} {- for IO -}
module EX-multichannel where

open import IO.Primitive

open import Agda.Builtin.Unit
open import Agda.Builtin.String

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; 0ℤ; +_; _≤ᵇ_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Function using (const; id; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

open import ST-multichannel

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

return : A → A × ⊤
return a = a , tt

server-p : MSession 1
server-p = recv zero int (recv zero int (send zero bool (close zero terminate)))

client-p : MSession 1
client-p = send zero int (send zero int (recv zero bool (close zero terminate)))

protocol : MSession 0
protocol = connect null client-p server-p refl

server : Cmd Bool ⊤ 1 server-p
server = RECV zero const $
         RECV zero _≤ᵇ_ $
         SEND zero return $
         CLOSE zero id $
         END (const false)

client : Cmd Bool ⊤ 1 client-p
client = SEND zero (const (+ 42 , tt)) $
         SEND zero (const (+ 17 , tt)) $
         RECV zero const $
         CLOSE zero id $
         END id

system : Cmd Bool ⊤ 0 protocol
system = CONNECT refl (λ x → x , x) null client server

main : IO ⊤
main = do
  putStrLn "Multichannel session types in action!"
  b ← runCmd system tt
  putStrLn $ if b then "true" else "false" 
\end{code}
