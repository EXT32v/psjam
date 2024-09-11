
{-# OPTIONS --termination-depth=2 #-}
{-# OPTIONS --guardedness #-}

module Main where

-- https://www.acmicpc.net/problem/26259

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
open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ) renaming (_+_ to _+ᵢ_; _≤_ to _≤ᵢ_)
open import Function.Base using (case_of_)
open import Data.Integer.Properties as IP
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary
open import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality.Core renaming (sym to ≡-sym; trans to ≡-trans)


-- Tools
splitBool : (b : Bool) → (b ≡ false) ⊎ (b ≡ true)
splitBool false = inj₁ refl
splitBool true = inj₂ refl

-- Backroom
module Backroom
  (m n : ℕ) {0<m : 0 < m} {0<n : 0 < n}
  (rWall : (x : ℕ) → .{suc x < m} → (y : ℕ) → .{y < n} → Bool)
  (dWall : (x : ℕ) → .{x < m} → (y : ℕ) → .{suc y < n} → Bool)
  (scoreF : (x : ℕ) → .{x < m} → (y : ℕ) → .{y < n} → ℤ) where

  data Got : ℕ → ℕ → ℤ → Set where
    start : Got zero zero (scoreF zero {0<m} zero {0<n})
    right : {x : ℕ} → .{sucx<m : suc x < m}
          → {y : ℕ} → .{y<n : y < n}
          → {oldScore : ℤ}
          → Got x y oldScore
          → (rWall x {sucx<m} y {y<n}) ≡ false
          → Got (suc x) y (oldScore +ᵢ (scoreF (suc x) {sucx<m} y {y<n}))
    down  : {x : ℕ} → .{x<m : x < m}
          → {y : ℕ} → .{sucy<n : suc y < n}
          → {oldScore : ℤ}
          → Got x y oldScore
          → (dWall x {x<m} y {sucy<n}) ≡ false
          → Got x (suc y) (oldScore +ᵢ (scoreF x {x<m} (suc y) {sucy<n}))

  MaxGot : ℕ → ℕ → ℤ → Set
  MaxGot x y maxScore = (Got x y maxScore) × ({score : ℤ} → (Got x y score) → score ≤ᵢ maxScore)

  CannotGot : ℕ → ℕ → Set
  CannotGot x y = {score : ℤ} → ¬ (Got x y score)

  maxGot00 : MaxGot zero zero (scoreF zero {0<m} zero {0<n})
  maxGot00 = (start , λ {score} → λ { start → (IP.≤-reflexive refl) })

  maxGotRight0 :
    {x : ℕ} → .{sucx<m : suc x < m}
    → {fromScore : ℤ}
    → MaxGot x zero fromScore
    → (rWall x {sucx<m} 0 {0<n}) ≡ false
    → MaxGot (suc x) zero (fromScore +ᵢ (scoreF (suc x) {sucx<m} zero {0<n}))
  maxGotRight0 (fromGot , fromGotIsMax) rw =
    (
      right fromGot rw ,
      λ {hScore} → λ {
        (right hFromGot _) → IP.+-mono-≤ (fromGotIsMax hFromGot) (IP.≤-reflexive refl)
      }
    )

  maxGotDown0 :
    {y : ℕ} → .{sucy<n : suc y < n}
    → {fromScore : ℤ}
    → MaxGot zero y fromScore
    → (dWall 0 {0<m} y {sucy<n}) ≡ false
    → MaxGot zero (suc y) (fromScore +ᵢ (scoreF zero {0<m} (suc y) {sucy<n}))
  maxGotDown0 (fromGot , fromGotIsMax) rw =
    (
      down fromGot rw ,
      λ {hScore} → λ {
        (down hFromGot _) → IP.+-mono-≤ (fromGotIsMax hFromGot) (IP.≤-reflexive refl)
      }
    )
  
  cannotGotRight0 :
    {x : ℕ}
    → CannotGot x 0
    → CannotGot (suc x) 0
  cannotGotRight0 fromCg (right leftGot _) = fromCg leftGot

  cannotGotDown0 :
    {y : ℕ}
    → CannotGot 0 y
    → CannotGot 0 (suc y)
  cannotGotDown0 fromCg (down upGot _) = fromCg upGot

  cannotGot :
    {x y : ℕ}
    → CannotGot (suc x) y
    → CannotGot x (suc y)
    → CannotGot (suc x) (suc y)
  cannotGot cgU cgL (right got _) = cgL got
  cannotGot cgU cgL (down got _) = cgU got

  cannotGotWallDown :
    {x : ℕ} → .{sucx<m : suc x < m} → {y : ℕ} → .{sucy<n : suc y < n}
    → CannotGot x (suc y)
    → dWall (suc x) {sucx<m} y {sucy<n} ≡ true
    → CannotGot (suc x) (suc y)
  cannotGotWallDown cg wall (right got _) = cg got
  cannotGotWallDown cg (wall) (down got noWall) = case (≡-trans (≡-sym wall) noWall) of λ ()

  cannotGotWallRight :
    {x : ℕ} → .{sucx<m : suc x < m} → {y : ℕ} → .{sucy<n : suc y < n}
    → CannotGot (suc x) y
    → rWall x {sucx<m} (suc y) {sucy<n} ≡ true
    → CannotGot (suc x) (suc y)
  cannotGotWallRight cg wall (down got _) = cg got
  cannotGotWallRight cg (wall) (right got noWall) = case (≡-trans (≡-sym wall) noWall) of λ ()

  cannotGotWall :
    {x : ℕ} → .{sucx<m : suc x < m} → {y : ℕ} → .{sucy<n : suc y < n}
    → dWall (suc x) {sucx<m} y {sucy<n} ≡ true
    → rWall x {sucx<m} (suc y) {sucy<n} ≡ true
    → CannotGot (suc x) (suc y)
  cannotGotWall dw rw (right got wall) = case (≡-trans (≡-sym wall) rw) of λ ()
  cannotGotWall dw rw (down got wall) = case (≡-trans (≡-sym wall) dw) of λ ()

  bakaFibo : (x : ℕ) .{x<m : x < m} → (y : ℕ) .{y<n : y < n} → (Σ ℤ (MaxGot x y)) ⊎ (CannotGot x y)
  bakaFibo zero {0<m} zero {0<n} = inj₁ ((scoreF zero {0<m} zero {0<n}) , maxGot00)
  bakaFibo zero {0<m} (suc y) {sucy<n} =
    case (bakaFibo zero {0<m} y {NP.<-trans (NP.n<1+n _) sucy<n}) of λ {
      (inj₁ (x₁ , x₂)) → case (splitBool (dWall zero y)) of λ {
        (inj₁ wall≡false) → inj₁ (_ , maxGotDown0 {_} {sucy<n} x₂ wall≡false)
      ; (inj₂ wall≡true) → {!   !}
      }
    ; (inj₂ x) → inj₂ {!   !}
    }
  bakaFibo (suc x) {x<m} zero {y<n} = {!   !}
  bakaFibo (suc x) {x<m} (suc y) {y<n} = {!   !}
-- 
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

fibo' : (key : ℕ) → Memo ℕ P (Σ ℕ (λ v → ({k : ℕ} {_ : ⊤} → k ≡ key → P k v)))
fibo' zero = do
  return (1 , λ { refl → refl } )
fibo' (suc zero) = do
  return (1 , λ { refl → refl } )
fibo' (suc (suc n)) = do
  (fibo'-n , h1) ← memo (fibo' n)
  (fibo'-suc-n , h2) ← memo (fibo' (suc n))
  let ang1 = h1 refl
      ang2 = h2 refl
  return ((fibo'-n + fibo'-suc-n) % 1000000007 , λ {k} {_} → λ { refl → case ang1 of λ { refl → case ang2 of λ { refl → refl } } })

fibo : (key : ℕ) → (Σ ℕ (λ v → ({k : ℕ} {_ : ⊤} → k ≡ key → P k v)))
fibo key = runMemo (fibo' key)

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
        -- let pmap = execMemo (fibo' i)
            -- l = toList (PMap.map pmap)
        let (o , _) = fibo i
        putStrLn (Data.Nat.Show.show o)
        -- putStrLn (concat ((λ (key , value) → "W " ++ (Data.Nat.Show.show key) ++ " " ++ (Data.Nat.Show.show value) ++ "\n") <$> l))
    ; nothing → return tt
    }) 