{-# OPTIONS --termination-depth=2 #-}
{-# OPTIONS --guardedness #-}

module Fibo where

open import Function.Base using (case_of_)
open import Data.Nat
open import Agda.Builtin.Equality
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Effect.Monad
open RawMonad {{...}}
open import Data.Product using (Σ; _,_; _×_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Memo (<-strictTotalOrder)
open import Data.Tree.AVL (<-strictTotalOrder)

open StrictTotalOrder <-strictTotalOrder

-- Fibo example
bakaFibo : ℕ → ℕ
bakaFibo zero = 1
bakaFibo (suc zero) = 1
bakaFibo (suc (suc n)) = (bakaFibo n + bakaFibo (suc n)) % 1000000007

P : ℕ → ℕ → Set
P i o = bakaFibo i ≡ o

open import Level using (Level)
repeat : {l₁ l₂ : Level} → {M : Set l₁ → Set l₂} → {{RawMonad M}} → ℕ → M ⊤ → M ⊤
repeat zero io = return tt
repeat (suc n) io = do
  repeat n io
  io

fibo' : (key : ℕ) → Memo ℕ P (Σ ℕ (λ v → (P key v × ⊤)))
fibo' zero = do
  return (1 , (refl , _) )
fibo' (suc zero) = do
  return (1 , (refl , _) )
fibo' (suc (suc n)) = do
  (fibo'-n , (h1 , _)) ← memo {_} {_} {_} {_} {n} (fibo' n)
  (fibo'-suc-n , (h2 , _)) ← memo {_} {_} {_} {_} {suc n} (fibo' (suc n))
  return ((fibo'-n + fibo'-suc-n) % 1000000007 , ((case h1 of λ { refl → case h2 of λ { refl → refl } }) , _))

fibo : (key : ℕ) → (Σ ℕ (λ v → (P key v × ⊤)))
fibo key = runMemo (λ { refl → λ x → x }) (fibo' key)

open import IO using (IO; Main; run; getLine; putStrLn)
import IO.Instances
open import Data.String using (String; concat; _++_)
import Data.List.Instances
open import Level
import Data.Nat.Show
open import Data.Maybe using (Maybe; just; nothing)

main : Main
main = run do
  s ← getLine
  let maybeN = Data.Nat.Show.readMaybe 10 s
  case maybeN of (λ
    { (just i) → do
        let (o , _) = fibo i
        putStrLn (Data.Nat.Show.show o)
    ; nothing → return tt
    })