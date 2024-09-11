
{-# OPTIONS --termination-depth=40 #-}
{-# OPTIONS --guardedness #-}

module Main where

-- https://www.acmicpc.net/problem/26259

open import Function.Base using (case_of_)
open import Data.Nat
open import Agda.Builtin.Equality
open import Effect.Monad
open RawMonad {{...}}
open import Data.Product using (Σ; _,_; _×_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ) renaming (_+_ to _+ᵢ_; _≤_ to _≤ᵢ_; _⊔_ to _⊔ᵢ_; _≤?_ to _≤?ᵢ_)
open import Function.Base using (case_of_)
open import Data.Integer.Properties as IP
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary
open import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality.Core renaming (subst to ≡-subst; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary.Decidable using (_because_)
open import Relation.Nullary.Reflects
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Maybe using (Maybe; just; nothing)

open import Memo (×-strictTotalOrder NP.<-strictTotalOrder NP.<-strictTotalOrder)


-- Tools
splitBool : (b : Bool) → (b ≡ false) ⊎ (b ≡ true)
splitBool false = inj₁ refl
splitBool true = inj₂ refl

-- Backroom
module Backroom
  (rWall : (x : ℕ) → (y : ℕ) → Bool)
  (dWall : (x : ℕ) → (y : ℕ) → Bool)
  (scoreF : (x : ℕ) → (y : ℕ) → ℤ) where

  data Got : ℕ → ℕ → ℤ → Set where
    start : Got zero zero (scoreF zero zero)
    right : {x y : ℕ}
          → {oldScore : ℤ}
          → Got x y oldScore
          → (rWall x y) ≡ false
          → Got (suc x) y (oldScore +ᵢ (scoreF (suc x) y))
    down  : {x y : ℕ}
          → {oldScore : ℤ}
          → Got x y oldScore
          → (dWall x y) ≡ false
          → Got x (suc y) (oldScore +ᵢ (scoreF x (suc y)))

  MaxGot : ℕ → ℕ → ℤ → Set
  MaxGot x y maxScore = (Got x y maxScore) × ({score : ℤ} → (Got x y score) → score ≤ᵢ maxScore)

  CannotGot : ℕ → ℕ → Set
  CannotGot x y = {score : ℤ} → ¬ (Got x y score)

  maxGot00 : MaxGot zero zero (scoreF zero zero)
  maxGot00 = (start , λ {score} → λ { start → (IP.≤-reflexive refl) })

  maxGotRight0 :
    {x : ℕ}
    → {fromScore : ℤ}
    → MaxGot x zero fromScore
    → (rWall x zero) ≡ false
    → MaxGot (suc x) zero (fromScore +ᵢ (scoreF (suc x) zero))
  maxGotRight0 (fromGot , fromGotIsMax) norw =
    (
      right fromGot norw ,
      λ {hScore} → λ {
        (right hFromGot _) → IP.+-mono-≤ (fromGotIsMax hFromGot) (IP.≤-reflexive refl)
      }
    )

  maxGotDown0 :
    {y : ℕ}
    → {fromScore : ℤ}
    → MaxGot zero y fromScore
    → (dWall 0 y) ≡ false
    → MaxGot zero (suc y) (fromScore +ᵢ (scoreF zero (suc y)))
  maxGotDown0 (fromGot , fromGotIsMax) nodw =
    (
      down fromGot nodw ,
      λ {hScore} → λ {
        (down hFromGot _) → IP.+-mono-≤ (fromGotIsMax hFromGot) (IP.≤-reflexive refl)
      }
    )
  
  maxGotRight :
    {x y : ℕ}
    → {fromScore : ℤ}
    → MaxGot x (suc y) fromScore
    → (dWall (suc x) y) ≡ true
    → (rWall x (suc y)) ≡ false
    → MaxGot (suc x) (suc y) (fromScore +ᵢ (scoreF (suc x) (suc y)))
  maxGotRight (fromGot , fromGotIsMax) dw norw =
    (
      right fromGot norw ,
      λ {hScore} → λ {
        (right hFromGot _) → IP.+-mono-≤ (fromGotIsMax hFromGot) (IP.≤-reflexive refl)
      ; (down _ nodw) → case (≡-trans (≡-sym dw) nodw) of λ ()
      }
    )
  
  maxGotDown :
    {x y : ℕ}
    → {fromScore : ℤ}
    → MaxGot (suc x) y fromScore
    → (rWall x (suc y)) ≡ true
    → (dWall (suc x) y) ≡ false
    → MaxGot (suc x) (suc y) (fromScore +ᵢ (scoreF (suc x) (suc y)))
  maxGotDown (fromGot , fromGotIsMax) rw nodw =
    (
      down fromGot nodw ,
      λ {hScore} → λ {
        (down hFromGot _) → IP.+-mono-≤ (fromGotIsMax hFromGot) (IP.≤-reflexive refl)
      ; (right _ norw) → case (≡-trans (≡-sym rw) norw) of λ ()
      }
    )

  maxGotCannotGotRight :
    {x y : ℕ}
    → {fromScore : ℤ}
    → MaxGot x (suc y) fromScore
    → CannotGot (suc x) y
    → (rWall x (suc y)) ≡ false
    → MaxGot (suc x) (suc y) (fromScore +ᵢ (scoreF (suc x) (suc y)))
  maxGotCannotGotRight (fromGot , fromGotIsMax) cg norw =
    (
      right fromGot norw ,
      λ {hScore} → λ {
        (right hFromGot _) → IP.+-mono-≤ (fromGotIsMax hFromGot) (IP.≤-reflexive refl)
      ; (down hFromGot _) → case (cg hFromGot) of λ ()
      }
    )

  maxGotCannotGotDown :
    {x y : ℕ}
    → {fromScore : ℤ}
    → MaxGot (suc x) y fromScore
    → CannotGot x (suc y)
    → (dWall (suc x) y) ≡ false
    → MaxGot (suc x) (suc y) (fromScore +ᵢ (scoreF (suc x) (suc y)))
  maxGotCannotGotDown (fromGot , fromGotIsMax) cg nodw =
    (
      down fromGot nodw ,
      λ {hScore} → λ {
        (down hFromGot _) → IP.+-mono-≤ (fromGotIsMax hFromGot) (IP.≤-reflexive refl)
      ; (right hFromGot _) → case (cg hFromGot) of λ ()
      }
    )
  
  maxGot : 
    {x y : ℕ}
    → {fromScoreL : ℤ}
    → {fromScoreU : ℤ}
    → MaxGot x (suc y) fromScoreL
    → MaxGot (suc x) y fromScoreU
    → (rWall x (suc y)) ≡ false
    → (dWall (suc x) y) ≡ false
    → MaxGot (suc x) (suc y) ((fromScoreL ⊔ᵢ fromScoreU) +ᵢ (scoreF (suc x) (suc y)))
  maxGot {x} {y} {fromScoreL} {fromScoreU} (fromGotL , fromGotIsMaxL) (fromGotU , fromGotIsMaxU) norw nodw =
    case (fromScoreL ≤?ᵢ fromScoreU) of λ {
      (true because (ofʸ fromScoreL≤fromScoreU)) → 
        ≡-subst (λ z → MaxGot (suc x) (suc y) (z +ᵢ (scoreF (suc x) (suc y)))) (≡-sym (IP.i≤j⇒i⊔j≡j fromScoreL≤fromScoreU)) (
          down fromGotU nodw ,
          λ {hScore} → λ {
              (right hFromGot _) → IP.+-mono-≤ (IP.≤-trans (fromGotIsMaxL hFromGot) fromScoreL≤fromScoreU) (IP.≤-reflexive refl)
            ; (down hFromGot _) → IP.+-mono-≤ (fromGotIsMaxU hFromGot) (IP.≤-reflexive refl)
            }
        )
    ; (false because (ofⁿ ¬fromScoreL≤fromScoreU)) →
        let
          fromScoreU≤fromScoreL = IP.<⇒≤ (IP.≰⇒> ¬fromScoreL≤fromScoreU)
        in
        ≡-subst (λ z → MaxGot (suc x) (suc y) (z +ᵢ (scoreF (suc x) (suc y)))) (≡-sym (IP.i≥j⇒i⊔j≡i fromScoreU≤fromScoreL)) (
          right fromGotL norw ,
          λ {hScore} → λ {
              (down hFromGot _) → IP.+-mono-≤ (IP.≤-trans (fromGotIsMaxU hFromGot) fromScoreU≤fromScoreL) (IP.≤-reflexive refl)
            ; (right hFromGot _) → IP.+-mono-≤ (fromGotIsMaxL hFromGot) (IP.≤-reflexive refl)
            }
        )
    }
  
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

  cannotGotWallDown0 :
    {y : ℕ}
    → dWall zero y ≡ true
    → CannotGot zero (suc y)
  cannotGotWallDown0 wall (down got noWall) = case (≡-trans (≡-sym wall) noWall) of λ ()

  cannotGotWallRight0 :
    {x : ℕ}
    → rWall x zero ≡ true
    → CannotGot (suc x) zero
  cannotGotWallRight0 wall (right got noWall) = case (≡-trans (≡-sym wall) noWall) of λ ()

  cannotGotWallDown :
    {x y : ℕ}
    → CannotGot x (suc y)
    → dWall (suc x) y ≡ true
    → CannotGot (suc x) (suc y)
  cannotGotWallDown cg wall (right got _) = cg got
  cannotGotWallDown cg (wall) (down got noWall) = case (≡-trans (≡-sym wall) noWall) of λ ()

  cannotGotWallRight :
    {x y : ℕ}
    → CannotGot (suc x) y
    → rWall x (suc y) ≡ true
    → CannotGot (suc x) (suc y)
  cannotGotWallRight cg wall (down got _) = cg got
  cannotGotWallRight cg (wall) (right got noWall) = case (≡-trans (≡-sym wall) noWall) of λ ()

  cannotGotWall :
    {x y : ℕ}
    → dWall (suc x) y ≡ true
    → rWall x (suc y) ≡ true
    → CannotGot (suc x) (suc y)
  cannotGotWall dw rw (right got wall) = case (≡-trans (≡-sym wall) rw) of λ ()
  cannotGotWall dw rw (down got wall) = case (≡-trans (≡-sym wall) dw) of λ ()

  bakaSolution : (x y : ℕ) → (Σ ℤ (MaxGot x y)) ⊎ (CannotGot x y)
  bakaSolution zero zero = inj₁ ((scoreF zero zero) , maxGot00)
  bakaSolution zero (suc y) =
    case (bakaSolution zero y) of λ {
      (inj₁ (_ , got)) → case (splitBool (dWall zero y)) of λ {
        (inj₁ wall≡false) → inj₁ (_ , maxGotDown0 got wall≡false)
      ; (inj₂ wall≡true) → inj₂ (λ {s} → cannotGotWallDown0 wall≡true)
      }
    ; (inj₂ cg) → inj₂ (cannotGotDown0 cg)
    }
  bakaSolution (suc x) zero = 
    case (bakaSolution x zero) of λ {
      (inj₁ (_ , got)) → case (splitBool (rWall x zero)) of λ {
        (inj₁ wall≡false) → inj₁ (_ , maxGotRight0 got wall≡false)
      ; (inj₂ wall≡true) → inj₂ (λ {_} → cannotGotWallRight0 wall≡true)
      }
    ; (inj₂ cg) → inj₂ (cannotGotRight0 cg)
    }
  bakaSolution (suc x) (suc y) =
      case (splitBool (rWall x (suc y))) of λ {
        (inj₁ rwall≡false) → case (splitBool (dWall (suc x) y)) of λ {
          (inj₁ dwall≡false) → case (bakaSolution x (suc y)) of λ {
            (inj₁ (_ , lgot)) → case (bakaSolution (suc x) y) of λ {
              (inj₁ (_ , ugot)) → inj₁ (_ , maxGot lgot ugot rwall≡false dwall≡false)
            ; (inj₂ ucg) → inj₁ (_ , maxGotCannotGotRight lgot ucg rwall≡false)
            }
          ; (inj₂ lcg) → case (bakaSolution (suc x) y) of λ {
              (inj₁ (_ , ugot)) → inj₁ (_ , maxGotCannotGotDown ugot lcg dwall≡false)
            ; (inj₂ ucg) → inj₂ (λ {_} → cannotGot ucg lcg)
            }
          }
        ; (inj₂ dwall≡true) → case (bakaSolution x (suc y)) of λ {
            (inj₁ (_ , lgot)) → inj₁ (_ , maxGotRight lgot dwall≡true rwall≡false)
          ; (inj₂ lcg) → inj₂ (λ {_} → cannotGotWallDown lcg dwall≡true)
          }
        }
      ; (inj₂ rwall≡true) → case (splitBool (dWall (suc x) y)) of λ {
          (inj₁ dwall≡false) → case (bakaSolution (suc x) y) of λ {
            (inj₁ (_ , ugot)) → inj₁ (_ , maxGotDown ugot rwall≡true dwall≡false)
          ; (inj₂ ucg) → inj₂ (λ {_} → cannotGotWallRight ucg rwall≡true)
          }
        ; (inj₂ dwall≡true) → inj₂ (λ {_} → cannotGotWall dwall≡true rwall≡true)
        }
      }
  
  P : (ℕ × ℕ) → (Maybe ℤ) → Set
  P (x , y) (just score) = MaxGot x y score
  P (x , y) nothing = CannotGot x y

  solution' : ((x , y) : ℕ × ℕ) → Memo (Maybe ℤ) P (Σ (Maybe ℤ) (λ v → (P (x , y) v × ⊤)))
  solution' (zero , zero) = return (just (scoreF zero zero) , (maxGot00 , _))
  solution' (zero , (suc y)) = do
    s_zero_y ← memo (solution' (zero , y))
    return (
      case s_zero_y of λ {
        (just _ , (got , _)) → case (splitBool (dWall zero y)) of λ {
          (inj₁ wall≡false) → (just _ , (maxGotDown0 got wall≡false , _))
        ; (inj₂ wall≡true) → (nothing , ((λ {_} → cannotGotWallDown0 wall≡true) , _))
        }
      ; (nothing , (cg , _)) → (nothing , ((λ {_} → (cannotGotDown0 cg)) , _))
      }
      )
  solution' ((suc x) , zero) = do
    s_x_zero ← memo (solution' (x , zero))
    return (
      case s_x_zero of λ {
        (just _ , (got , _)) → case (splitBool (rWall x zero)) of λ {
          (inj₁ wall≡false) → (just _ , (maxGotRight0 got wall≡false , _))
        ; (inj₂ wall≡true) → (nothing , ((λ {_} → cannotGotWallRight0 wall≡true) , _))
        }
      ; (nothing , (cg , _)) → (nothing , ((λ {_} → cannotGotRight0 cg) , _))
      }
      )
  solution' (suc x , suc y) = do
    s_x_sucy ← memo (solution' (x , suc y))
    s_sucx_y ← memo (solution' (suc x , y))
    case (splitBool (rWall x (suc y))) of λ {
        (inj₁ rwall≡false) → case (splitBool (dWall (suc x) y)) of λ {
          (inj₁ dwall≡false) →
            case s_x_sucy of λ {
                (just _ , (lgot , _)) →
                  return
                    (case s_sucx_y of λ {
                      (just _ , (ugot , _)) → (just _ , (maxGot lgot ugot rwall≡false dwall≡false , _))
                    ; (nothing , (ucg , _)) → (just _ , (maxGotCannotGotRight lgot ucg rwall≡false , _))
                    })
              ; (nothing , (lcg , _)) →
                  return
                    (case s_sucx_y of λ {
                      (just _ , (ugot , _)) → (just _ , (maxGotCannotGotDown ugot lcg dwall≡false , _))
                    ; (nothing , (ucg , _)) → (nothing , ((λ {_} → cannotGot ucg lcg) , _))
                    })
              }
        ; (inj₂ dwall≡true) →
            return
              (case s_x_sucy of λ {
                (just _ , (lgot , _)) → (just _ , (maxGotRight lgot dwall≡true rwall≡false , _))
              ; (nothing , (lcg , _)) → (nothing , ((λ {_} → cannotGotWallDown lcg dwall≡true) , _))
              })
        }
      ; (inj₂ rwall≡true) → case (splitBool (dWall (suc x) y)) of λ {
          (inj₁ dwall≡false) →
            return
              (case s_sucx_y of λ {
                (just _ , (ugot , _)) → (just _ , (maxGotDown ugot rwall≡true dwall≡false , _))
              ; (nothing , (ucg , _)) → (nothing , ((λ {_} → cannotGotWallRight ucg rwall≡true) , _))
              })
        ; (inj₂ dwall≡true) → return (nothing , ((λ {_} → cannotGotWall dwall≡true rwall≡true) , _))
        }
      }

  solution : ((x , y) : ℕ × ℕ) → Σ (Maybe ℤ) (λ v → (P (x , y) v × ⊤))
  solution i = runMemo (λ (h1 , h2) → case h1 of λ { refl → case h2 of λ { refl → λ x → x } } ) (solution' i)
  
  -- Trace!
  open import Data.Nat.Show using (show)
  open import Data.String using (String; _++_)
  trace : {x y : ℕ} → {score : ℤ} → Got x y score → String
  trace start = "(0,0)"
  trace (right {x} {y} got _) = (trace got) ++ " - (" ++ (show (suc x)) ++ "," ++ (show y) ++ ")"
  trace (down {x} {y} got _) = (trace got) ++ " - (" ++ (show x) ++ "," ++ (show (suc y)) ++ ")"


open import IO using (IO; Main; run; getLine; putStrLn)
import IO.Instances
open import Data.String using (String; concat; _++_; words; uncons; fromChar)
import Data.List.Instances
open import Data.List using (List; foldr; foldl; _∷_; []; replicate; upTo) renaming (uncons to unconsₗ)
import Data.Nat.Show
import Data.Integer.Show
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Effectful.Transformer using (MaybeT; mkMaybeT; runMaybeT)
import Data.Maybe.Instances
open import Data.Integer using (_◃_)
open import Data.Sign using (Sign)
open RawMonadTd {{...}} using (lift)
open import Data.Bool using (_∧_)

open import Data.Tree.AVL.Map (×-strictTotalOrder NP.<-strictTotalOrder NP.<-strictTotalOrder) using (Map; lookup; insert; empty)

readIntMaybe10 : String → Maybe ℤ
readIntMaybe10 str = (case (uncons str) of λ {
    (just ('-' , s)) → (Sign.- ◃_) <$> (Data.Nat.Show.readMaybe 10 s)
  ; (just (c , s)) → (Sign.+ ◃_) <$> (Data.Nat.Show.readMaybe 10 ((fromChar c) ++ s))
  ; nothing → nothing
  })

getLineInts : MaybeT IO (List ℤ)
getLineInts = do
  line ← lift getLine
  mkMaybeT (return (foldr
    (λ x l → do
      x' ← x
      l' ← l
      return (Data.List._∷_ x' l')
    )
    (return [])
    ((readIntMaybe10) <$> (words line))))

getLineNats : MaybeT IO (List ℕ)
getLineNats = do
  line ← lift getLine
  mkMaybeT (return (foldr
    (λ x l → do
      x' ← x
      l' ← l
      return (Data.List._∷_ x' l')
    )
    (return [])
    ((Data.Nat.Show.readMaybe 10) <$> (words line))))

getScoreMap : (n : ℕ) → MaybeT IO (Map ℤ)
getScoreMap n =
  foldl (λ mapM x → do
      map ← mapM
      ints ← getLineInts
      return (Σ.proj₂ (foldl (λ (y , map) score → (suc y , insert (x , y) score map)) (zero , map) ints))
    ) (return empty) (upTo n)

mmain : MaybeT IO ⊤
mmain = do
  nms ← getLineNats
  (n , ms) ← mkMaybeT (return (unconsₗ nms))
  (m , _) ← mkMaybeT (return (unconsₗ ms))
  scoreMap ← getScoreMap n
  
  x1y1x2y2s ← getLineNats
  (x1 , y1x2y2s) ← mkMaybeT (return (unconsₗ x1y1x2y2s))
  (y1 , x2y2s) ← mkMaybeT (return (unconsₗ y1x2y2s))
  (x2 , y2s) ← mkMaybeT (return (unconsₗ x2y2s))
  (y2 , _) ← mkMaybeT (return (unconsₗ y2s))

  let rwall×dwall : (ℕ → ℕ → Bool) × (ℕ → ℕ → Bool)
      rwall×dwall =
        case (x1 ≡ᵇ x2) of λ {
          true →  case (y1 ≡ᵇ y2) of λ {
                    true → (λ _ _ → false) , (λ _ _ → false)
                  ; false → (λ x y → (suc x ≡ᵇ x1) ∧ ((y1 ⊓ y2) ≤ᵇ y) ∧ (y <ᵇ (y1 ⊔ y2))) , (λ _ _ → false)
                  }
        ; false → case (y1 ≡ᵇ y2) of λ {
                    true → (λ _ _ → false) , (λ x y → (suc y ≡ᵇ y1) ∧ ((x1 ⊓ x2) ≤ᵇ x) ∧ (x <ᵇ (x1 ⊔ x2)))
                  ; false → (λ _ _ → false) , (λ _ _ → false)
                  }
        }
      
      rwall = Σ.proj₁ rwall×dwall
      dwall = Σ.proj₂ rwall×dwall

      scoreF : ℕ → ℕ → ℤ
      scoreF x y = case (lookup scoreMap (x , y)) of λ { (just score) → score ; nothing → Data.Integer.0ℤ }
  
      ans×proof = Backroom.solution rwall dwall scoreF (pred n , pred m)

  case ans×proof of λ {
      (just score , ((got , _) , _)) → do
        mkMaybeT (return <$> (putStrLn (Data.Integer.Show.show score)))
        mkMaybeT (return <$> (putStrLn (Backroom.trace rwall dwall scoreF got)))
    ; (nothing , (cannotGot , _)) → do
        mkMaybeT (return <$> (putStrLn "Entity"))
    }

main : Main
main = run do
  runMaybeT mmain
  return tt
