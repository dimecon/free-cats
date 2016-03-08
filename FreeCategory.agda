module FreeCategory where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.SetoidReasoning as ≈-Reasoning


module Carrier (A : Set) (C : A → A → Set) where

  data ExpCategory : A → A → Set where
    Embed : ∀ {a a′}
          → C a a′
          → ExpCategory a a′
    Id    : ∀ {a}
          → ExpCategory a a
    _⟫_   : ∀ {a a′ a′′}
          → ExpCategory a a′
          → ExpCategory a′ a′′
          → ExpCategory a a′′

  data EquivCategory : ∀ {a a′}
                     → ExpCategory a a′
                     → ExpCategory a a′
                     → Set where
    equiv-refl : ∀ {a a′}
               → {e : ExpCategory a a′}
               → EquivCategory e e
    equiv-sym : ∀ {a a′}
              → {e₁ e₂ : ExpCategory a a′}
              → EquivCategory e₁ e₂
              → EquivCategory e₂ e₁
    equiv-trans : ∀ {a a′}
                → {e₁ e₂ e₃ : ExpCategory a a′}
                → EquivCategory e₁ e₂
                → EquivCategory e₂ e₃
                → EquivCategory e₁ e₃
    equiv-cong : ∀ {a a′ a′′}
               → {e₁  e₂  : ExpCategory a a′}
               → {e₁′ e₂′ : ExpCategory a′ a′′}
               → EquivCategory e₁  e₂
               → EquivCategory e₁′ e₂′
               → EquivCategory (e₁ ⟫ e₁′) (e₂ ⟫ e₂′)
    left-id-id : ∀ {a a′}
               → {e : ExpCategory a a′}
               → EquivCategory (Id ⟫ e) e
    right-id-id : ∀ {a a′}
                → {e : ExpCategory a a′}
                → EquivCategory (e ⟫ Id) e
    assoc-⟫ : ∀ {a a′ a′′ a′′′}
            → (e   : ExpCategory a a′)
            → (e′  : ExpCategory a′ a′′)
            → (e′′ : ExpCategory a′′ a′′′)
            → EquivCategory ((e ⟫ e′) ⟫ e′′) (e ⟫ (e′ ⟫ e′′))

  equiv-setoid : {a a′ : A} → Setoid _ _
  equiv-setoid {a} {a′} = record
    { Carrier = ExpCategory a a′
    ; _≈_ = EquivCategory
    ; isEquivalence = record
      { refl  = equiv-refl
      ; sym   = equiv-sym
      ; trans = equiv-trans
      }
    }

  infixr 4 _⟩⟫⟨_
  _⟩⟫⟨_ : ∀ {a a′ a′′}
        → {e₁  e₂  : ExpCategory a a′}
        → {e₁′ e₂′ : ExpCategory a′ a′′}
        → EquivCategory e₁  e₂
        → EquivCategory e₁′ e₂′
        → EquivCategory (e₁ ⟫ e₁′) (e₂ ⟫ e₂′)
  _⟩⟫⟨_ = equiv-cong


  infixr 6 _∷_
  data FreeCategory : A → A → Set where
    nil : ∀ {a}
        → FreeCategory a a
    _∷_ : ∀ {a a′ a′′}
        → C a a′
        → FreeCategory a′ a′′
        → FreeCategory a  a′′

  eqClass : ∀ {a a′} → ExpCategory a a′ → FreeCategory a a′
  eqClass = {!!}


  module Sound where
    open ≈-Reasoning

    sound : ∀ {a a′}
          → {e₁ e₂ : ExpCategory a a′}
          → eqClass e₁ ≡ eqClass e₂
          → EquivCategory e₁ e₂
    sound {e₁ = e₁} {e₂ = e₂} prf =
      begin⟨ equiv-setoid ⟩
        e₁
      ≈⟨ {!!} ⟩
        e₂
      ∎

  module Complete where
    open ≡-Reasoning

    complete : ∀ {a a′}
             → {e₁ e₂ : ExpCategory a a′}
             → EquivCategory e₁ e₂
             → eqClass e₁ ≡ eqClass e₂
    complete = {!!}
