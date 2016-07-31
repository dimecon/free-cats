module FreeCategory where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.SetoidReasoning as ≈-Reasoning

module Composition {ℓ} (A : Set ℓ) (C : A → A → Set ℓ) where

  data ExpCategory : A → A → Set ℓ where
    Embed : ∀ {a a′}
          → C a a′
          → ExpCategory a a′
    Id    : ∀ {a}
          → ExpCategory a a
    _<>_   : ∀ {a a′ a′′}
          → ExpCategory a a′
          → ExpCategory a′ a′′
          → ExpCategory a a′′

  data EquivCategory : ∀ {a a′}
                     → ExpCategory a a′
                     → ExpCategory a a′
                     → Set ℓ where
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
               → EquivCategory (e₁ <> e₁′) (e₂ <> e₂′)
    left-id-id : ∀ {a a′}
               → {e : ExpCategory a a′}
               → EquivCategory (Id <> e) e
    right-id-id : ∀ {a a′}
                → {e : ExpCategory a a′}
                → EquivCategory (e <> Id) e
    assoc-<> : ∀ {a a′ a′′ a′′′}
            → (e   : ExpCategory a a′)
            → (e′  : ExpCategory a′ a′′)
            → (e′′ : ExpCategory a′′ a′′′)
            → EquivCategory ((e <> e′) <> e′′) (e <> (e′ <> e′′))

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

  open ≈-Reasoning

  infixr 6 _∷_
  data FreeCategory : A → A → Set ℓ where
    nil : ∀ {a} → FreeCategory a a
    _∷_ : ∀ {a a′ a′′} → C a a′ → FreeCategory a′ a′′ → FreeCategory a  a′′

  _++_ : ∀ {a a′ a′′} → FreeCategory a a′ → FreeCategory a′ a′′ → FreeCategory a a′′
  nil ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  right-id-nil : ∀ {a a′} {xs : FreeCategory a a′} → xs ++ nil ≡ xs
  right-id-nil {xs = nil} = refl
  right-id-nil {xs = x ∷ xs} = cong (λ xs → x ∷ xs) (right-id-nil {xs = xs})

  assoc-++ : ∀ {a a′ a′′ a′′′} (xs : FreeCategory a a′) (ys : FreeCategory a′ a′′) (zs : FreeCategory a′′ a′′′)
           → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  assoc-++ nil  _ _ = refl
  assoc-++ (x ∷ xs) ys zs = cong (λ xs → x ∷ xs) (assoc-++ xs ys zs)

  exp→free : ∀ {a a′} → ExpCategory a a′ → FreeCategory a a′
  exp→free (Embed cf) = cf ∷ nil
  exp→free Id = nil
  exp→free (f <> g) = exp→free f ++ exp→free g

  free→exp : ∀ {a a′} → FreeCategory a a′ → ExpCategory a a′
  free→exp nil = Id
  free→exp (x ∷ xs) = Embed x <> free→exp xs

  resp-++ : ∀ {a a′ a′′} {xs : FreeCategory a a′} {ys : FreeCategory a′ a′′}
          → EquivCategory (free→exp (xs ++ ys)) (free→exp xs <> free→exp ys)
  resp-++ {xs = nil} {ys} =  equiv-sym left-id-id
  resp-++ {xs = x ∷ xs} {ys} = begin⟨ equiv-setoid ⟩
    (Embed x <> free→exp (xs ++ ys))
      ≈⟨ equiv-cong equiv-refl resp-++ ⟩
    Embed x <> (free→exp xs <> free→exp ys)
      ≈⟨ equiv-sym (assoc-<> (Embed x) (free→exp xs) (free→exp ys)) ⟩
    ((Embed x <> free→exp xs) <> free→exp ys) ∎

  free→exp-inv : ∀ {a a′} {e : ExpCategory a a′} → EquivCategory (free→exp (exp→free e)) e
  free→exp-inv {e = Embed x} = right-id-id
  free→exp-inv {e = Id} = equiv-refl
  free→exp-inv {e = e <> e′} = begin⟨ equiv-setoid ⟩
    free→exp (exp→free e ++ exp→free e′)
      ≈⟨ resp-++ ⟩
    free→exp (exp→free e) <> free→exp (exp→free e′)
      ≈⟨ equiv-cong free→exp-inv free→exp-inv ⟩
    (e <> e′) ∎

  resp-≡ : ∀ {a a′} {xs ys : FreeCategory a a′} → xs ≡ ys → EquivCategory (free→exp xs) (free→exp ys)
  resp-≡ {xs = nil} {.nil} refl = equiv-refl
  resp-≡ {xs = x ∷ xs} {.x ∷ .xs} refl = equiv-refl

  module Sound where
    sound : ∀ {a a′} {e e′ : ExpCategory a a′}
          → exp→free e ≡ exp→free e′
          → EquivCategory e e′
    sound {e = e} {e′ = e′} p = begin⟨ equiv-setoid ⟩
      e                        ≈⟨ equiv-sym free→exp-inv ⟩
      free→exp (exp→free e)  ≈⟨ resp-≡ p ⟩
      free→exp (exp→free e′) ≈⟨ free→exp-inv ⟩
      e′ ∎

  module Complete where
    complete : ∀ {a a′}
             → {e₁ e₂ : ExpCategory a a′}
             → EquivCategory e₁ e₂
             → exp→free e₁ ≡ exp→free e₂
    complete equiv-refl = refl
    complete (equiv-sym eq) = sym (complete eq)
    complete (equiv-trans p₁ p₂) = trans (complete p₁) (complete p₂)
    complete (equiv-cong p₁ p₂) = cong₂ _++_ (complete p₁) (complete p₂)
    complete left-id-id = refl
    complete right-id-id = right-id-nil
    complete (assoc-<> e₁ e₂ e₃) = assoc-++ (exp→free e₁) (exp→free e₂) (exp→free e₃)
