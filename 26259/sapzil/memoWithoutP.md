open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Level

module Memo
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)

open import Data.Tree.AVL.Map (strictTotalOrder)

open import Effect.Monad
open RawMonad {{...}}
import Effect.Monad.Identity.Instances
open import Effect.Monad.State using (State; RawMonadState)
import Effect.Monad.State.Instances
open RawMonadState {{...}}
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Function.Base using (case_of_)
open import Data.Product using (Σ)

private
  variable
    l₁ : Level
    V  : Set l₁
    A  : Set l₁

record Memo
    (V : Set (a ⊔ ℓ₂))
    (A : Set (a ⊔ ℓ₂)) : (Set (a ⊔ ℓ₂)) where
  field
    toState : State (Map V) A

getMap : Memo V (Map V)
getMap = record { toState = get }

putMap : Map V → Memo V ⊤
putMap map = record { toState = put map }

-- Structures
open import Effect.Functor
open import Effect.Applicative

functor : RawFunctor (Memo V)
functor = record {
    _<$>_ = λ f m → record { toState = f <$> (Memo.toState m) }
  }

applicative : RawApplicative (Memo V)
applicative = record {
    rawFunctor = functor
  ; pure = λ a → record { toState = pure a }
  ; _<*>_ = λ mf m → record { toState = (Memo.toState mf) <*> (Memo.toState m) } -- mf <*> (Memo.toState m)
  }

monad : RawMonad (Memo V)
monad = record {
    rawApplicative = applicative
  ; _>>=_ = λ m f → record { toState = (Memo.toState m) >>= λ a → (Memo.toState (f a)) }
  }

instance
  memoFunctor = functor
  memoApplicative = applicative
  memoMonad = monad

memo : (Key → Memo V V) → Key → Memo V V
memo f key = do
  map ← getMap
  let maybeValue = lookup map key
  case maybeValue of λ
    {
      (just value) → do
        return value
    ; nothing → do
        v ← f key
        putMap (insert key v map)
        return v
    }


-- Proof
private
  variable
    (P : Key → V → Set (a ⊔ ℓ₂))

goodMap : P → 

pMemo :
  (P : Key → V → Set (a ⊔ ℓ₂))
   → (f : (key : Key) → Memo V (Σ V (P key)))
   → (key : Key)
   → Memo V (Σ V (P key))
pMemo P f key = do
  map ← getMap
  let maybeValue = lookup map key
  case maybeValue of λ
    {
      (just value) → do
        ? -- return value
    ; nothing → do
        v ← f key
        putMap (insert key v map)
        return v
    }