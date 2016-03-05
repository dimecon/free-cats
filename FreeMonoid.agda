module FreeMonoid where

open import Monoid
open import Relation.Binary.PropositionalEquality


data ExpMonoid (A : Set) : Set where
  Embed : A → ExpMonoid A
  MEmpty : ExpMonoid A
  _<>_ : ExpMonoid A → ExpMonoid A → ExpMonoid A

data EquivMonoid {A : Set} : ExpMonoid A → ExpMonoid A → Set where
  equiv-refl : {e : ExpMonoid A}
             → EquivMonoid e e
  equiv-sym : {e₁ e₂ : ExpMonoid A}
            → EquivMonoid e₁ e₂ → EquivMonoid e₂ e₁
  equiv-trans : {e₁ e₂ e₃ : ExpMonoid A}
              → EquivMonoid e₁ e₂
              → EquivMonoid e₂ e₃
              → EquivMonoid e₁ e₃
  left-id-mempty : {e : ExpMonoid A}
                 → EquivMonoid (MEmpty <> e) e
  right-id-mempty : {e : ExpMonoid A}
                  → EquivMonoid (e <> MEmpty) e
  assoc-mappend : {e₁ e₂ e₃ : ExpMonoid A}
                → EquivMonoid ((e₁ <> e₂) <> e₃) (e₁ <> (e₂ <> e₃))

eqClass : {A : Set} → ExpMonoid A → List A
eqClass = {!!}

sound : {A : Set}
      → {e₁ e₂ : ExpMonoid A}
      → eqClass e₁ ≡ eqClass e₂
      → EquivMonoid e₁ e₂
sound = {!!}

complete : {A : Set}
         → {e₁ e₂ : ExpMonoid A}
         → EquivMonoid e₁ e₂
         → eqClass e₁ ≡ eqClass e₂
complete = {!!}
