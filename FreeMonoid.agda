module FreeMonoid where

open import Monoid
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.SetoidReasoning as ≈-Reasoning


module Carrier (A : Set) where

  data ExpMonoid : Set where
    Embed : A → ExpMonoid
    MEmpty : ExpMonoid
    _<>_ : ExpMonoid → ExpMonoid → ExpMonoid


  data EquivMonoid : ExpMonoid → ExpMonoid → Set where
    equiv-refl : {e : ExpMonoid}
               → EquivMonoid e e
    equiv-sym : {e₁ e₂ : ExpMonoid}
              → EquivMonoid e₁ e₂ → EquivMonoid e₂ e₁
    equiv-trans : {e₁ e₂ e₃ : ExpMonoid}
                → EquivMonoid e₁ e₂
                → EquivMonoid e₂ e₃
                → EquivMonoid e₁ e₃
    equiv-cong : {e₁ e₂ e₁′ e₂′ : ExpMonoid}
               → EquivMonoid e₁ e₁′
               → EquivMonoid e₂ e₂′
               → EquivMonoid (e₁ <> e₂) (e₁′ <> e₂′)
    left-id-mempty : {e : ExpMonoid}
                   → EquivMonoid (MEmpty <> e) e
    right-id-mempty : {e : ExpMonoid}
                    → EquivMonoid (e <> MEmpty) e
    assoc-mappend : (e₁ e₂ e₃ : ExpMonoid)
                  → EquivMonoid ((e₁ <> e₂) <> e₃) (e₁ <> (e₂ <> e₃))

  equiv-setoid : Setoid _ _
  equiv-setoid = record
    { Carrier = ExpMonoid
    ; _≈_ = EquivMonoid
    ; isEquivalence = record
      { refl  = equiv-refl
      ; sym   = equiv-sym
      ; trans = equiv-trans
      }
    }


  eqClass : ExpMonoid → List A
  eqClass = {!!}


  module Sound where
    open ≈-Reasoning

    sound : {e₁ e₂ : ExpMonoid}
          → eqClass e₁ ≡ eqClass e₂
          → EquivMonoid e₁ e₂
    sound {e₁} {e₂} prf =
      begin⟨ equiv-setoid ⟩
        e₁
      ≈⟨ {!!} ⟩
        e₂
      ∎

  module Complete where
    open ≡-Reasoning

    complete : {e₁ e₂ : ExpMonoid}
             → EquivMonoid e₁ e₂
             → eqClass e₁ ≡ eqClass e₂
    complete = {!!}
