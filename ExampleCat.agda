module ExampleCat where

open import Relation.Binary.PropositionalEquality

-- consider the following category
--    f
-- A --> B
-- |g    |h
-- v  i  v
-- C --> D

data MyObject : Set where
  A : MyObject
  B : MyObject
  C : MyObject
  D : MyObject

data MyMorphism : MyObject → MyObject → Set where
  id : ∀ {o} → MyMorphism o o
  f  : MyMorphism A B
  g  : MyMorphism A C
  h  : MyMorphism B D
  i  : MyMorphism C D
  j  : MyMorphism A D

_⟫_ : ∀ {o₁ o₂ o₃}
    → MyMorphism o₁ o₂
    → MyMorphism o₂ o₃
    → MyMorphism o₁ o₃
id ⟫ m  = m
m  ⟫ id = m
f  ⟫ h  = j
g  ⟫ i  = j

left-id-id⟫ : ∀ {o₁ o₂} → ∀ {m : MyMorphism o₁ o₂}
            → id ⟫ m ≡ m
left-id-id⟫ = refl

assoc-⟫ : ∀ {o₁ o₂ o₃ o₄}
        → ∀ (m₁ : MyMorphism o₁ o₂)
        → ∀ (m₂ : MyMorphism o₂ o₃)
        → ∀ (m₃ : MyMorphism o₃ o₄)
        → m₁ ⟫ (m₂ ⟫ m₃) ≡ (m₁ ⟫ m₂) ⟫ m₃
assoc-⟫ id w e = refl
assoc-⟫ f id e = refl
assoc-⟫ f h id = refl
assoc-⟫ g id e = refl
assoc-⟫ g i id = refl
assoc-⟫ h id e = refl
assoc-⟫ i id e = refl
assoc-⟫ j id e = refl

data FreeCategory {O : Set} (M : O → O → Set) : O → O → Set where
  nil : ∀ {o} → FreeCategory M o o
  _∷_ : ∀ {o₁ o₂ o₃}
      → M o₁ o₂
      → FreeCategory M o₂ o₃
      → FreeCategory M o₁ o₃

[fh] : FreeCategory MyMorphism A D
--[fh] = f ∷ (h ∷ nil)
[fh] = g ∷ (i ∷ nil)

_[∘]_ : ∀ {O} {M : O → O → Set} {o₁ o₂ o₃}
      → FreeCategory M o₁ o₂ → FreeCategory M o₂ o₃ → FreeCategory M o₁ o₃
nil [∘] b = b
(x ∷ a) [∘] b = x ∷ (a [∘] b)
