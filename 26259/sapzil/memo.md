memo :
   { l₁ l₂ : Level } {V : Set l₁ } {P : Key → V → Set l₂}
   → (f : (key : Key) → Memo V P (Σ V (λ v → ({k : Key} {_ : ⊤ {ℓ₂}} → (h : k ≈ key) → P k v))))
   → (key : Key)
   → Memo V P (Σ V (λ v → ({k : Key} {_ : ⊤ {ℓ₂}} → (h : k ≈ key) → P k v)))
memo f key = do
  map ← getMap
  let prop = PMap.prop map
      maybeValue = plookup map key
  case maybeValue of λ
    {
      (just (value , (_ , h))) → do
        let j = λ {k} → (PMap.prop map) {k} {value}
        return (value , λ {k} {_} (k≈key) → prop (≈-∈ₖᵥ k≈key h)) -- (PMap.prop map) h
        -- return value
    ; nothing → do
        ( v , vh ) ← f key
        putMap (pinsert key v vh map)
        return ( v , λ {k} {_} h → vh {k} h)
    } 
{-# INLINE memo #-}