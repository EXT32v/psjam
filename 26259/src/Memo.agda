open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Level

module Memo
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)

open import Data.Tree.AVL.Map (strictTotalOrder) using (Map; lookup; insert; empty)
open import Data.Tree.AVL.Map.Membership.Propositional (strictTotalOrder)
open import Data.Tree.AVL.Map.Membership.Propositional.Properties (strictTotalOrder)

open import Effect.Monad
open RawMonad {{...}}
import Effect.Monad.Identity.Instances
open import Effect.Monad.State using (State; RawMonadState; evalState; execState)
import Effect.Monad.State.Instances
open RawMonadState {{...}}
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Function.Base using (case_of_)
open import Data.Product using (Σ; _,′_; _,_; _×_)
open import Agda.Builtin.Equality
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (_Respectsˡ_)

private
  variable
    l₁ l₂ l₃ : Level
    V  : Set l₁
    P  : Key → V → Set l₂
    A  : Set l₃
    T  : Set l₂

-- Tools
mapJustEq : (m : Maybe T) → Maybe (Σ T (λ t → m ≡ just t)) 
mapJustEq (just x) = just ( x , refl )
mapJustEq nothing = nothing

-- Map with key, value proposition!
record PMap
    (V : Set l₁)
    (P : Key → V → Set l₂)
    : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ l₁ ⊔ l₂) where
  field
    map          : Map V
    prop         : {k : Key} → {v : V} → ( k , v ) ∈ₖᵥ map → P k v
    key-respects : P Respectsˡ _≈_

pempty : P Respectsˡ _≈_ → PMap V P
pempty res = record
  { map = empty
  ; prop = λ {k} {v} h → case (∈ₖᵥ-empty h) of (λ ())
  ; key-respects = res
  }

plookup : (m : PMap V P) → (key : Key) → Maybe (Σ V (λ v → (P key v) × ((key , v) ∈ₖᵥ (PMap.map m))))
plookup pmap key =
  let map = PMap.map pmap
      prop = PMap.prop pmap
      maybeValue = lookup map key
  in
  case (mapJustEq maybeValue) of (λ {
    (just ( value , e )) → let
      kv∈ₖᵥmap : ( key , value ) ∈ₖᵥ map
      kv∈ₖᵥmap = ∈ₖᵥ-lookup⁻ e
      in
      just ( value , (prop kv∈ₖᵥmap , kv∈ₖᵥmap) )
  ; nothing → nothing
  })

pinsert : (key : Key) → (value : V) → P key value → PMap V P → PMap V P
pinsert key value p pmap = 
  let map = PMap.map pmap
      prop = PMap.prop pmap
      key-respects = PMap.key-respects pmap
  in
  record {
    map = insert key value map
  ; prop = λ {k} {v} kv∈ₖᵥnewmap → (
      case (∈ₖᵥ-insert⁻ kv∈ₖᵥnewmap) of (λ {
        (inj₁ (k≈key , refl)) → key-respects (Eq.sym k≈key) p
      ; (inj₂ (_ , kv∈ₖᵥmap)) → prop kv∈ₖᵥmap
      })
    )
  ; key-respects = PMap.key-respects pmap
  }


-- Memo monad
record Memo
    (V : Set l₁)
    (P : Key → V → Set l₂)
    (A : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ l₁ ⊔ l₂))
    : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ l₁ ⊔ l₂) where
  field
    toState : State (PMap V P) A

runMemo : P Respectsˡ _≈_ → Memo V P A → A
runMemo res memo = evalState (Memo.toState memo) (pempty res)

getMap : Memo V P (PMap V P)
getMap = record { toState = get }

putMap : PMap V P → Memo V P ⊤
putMap map = record { toState = put map }

-- Structures
open import Effect.Functor
open import Effect.Applicative

functor : RawFunctor (Memo V P)
functor = record {
    _<$>_ = λ f m → record { toState = f <$> (Memo.toState m) }
  }

applicative : RawApplicative (Memo V P)
applicative = record {
    rawFunctor = functor
  ; pure = λ a → record { toState = pure a }
  ; _<*>_ = λ mf m → record { toState = (Memo.toState mf) <*> (Memo.toState m) } -- mf <*> (Memo.toState m)
  }

monad : RawMonad (Memo V P)
monad = record {
    rawApplicative = applicative
  ; _>>=_ = λ m f → record { toState = (Memo.toState m) >>= λ a → (Memo.toState (f a)) }
  }

instance
  memoFunctor = functor
  memoApplicative = applicative
  memoMonad = monad


-- Tool proofs 
≈-∈ₖᵥ : {k key : Key} {v : V} {m : Map V} → k ≈ key → (key , v) ∈ₖᵥ m → (k , v) ∈ₖᵥ m
≈-∈ₖᵥ k≈key keyv∈ₖᵥm = ∈ₖᵥ-Respectsˡ ( Eq.sym k≈key , _≡_.refl ) keyv∈ₖᵥm

memo :
  { l₁ l₂ : Level } {V : Set l₁ } {P : Key → V → Set l₂}
  → {key : Key}
  → (fkey : Memo V P (Σ V (λ v → (P key v × ⊤ {a ⊔ ℓ₁ ⊔ ℓ₂}))))
  → Memo V P (Σ V (λ v → (P key v × ⊤ {a ⊔ ℓ₁ ⊔ ℓ₂})))
memo {_} {_} {_} {_} {key} fkey = do
  map ← getMap
  let prop = PMap.prop map
      maybeValue = plookup map key
  case maybeValue of λ
    {
      (just (value , (_ , h))) → do
        return (value , (prop h , _))
    ; nothing → do
        ( v , (vh , _) ) ← fkey
        map ← getMap
        putMap (pinsert key v vh map)
        return ( v , (vh , _) )
    }
