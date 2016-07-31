module FreeMonoid where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.SetoidReasoning as ≈-Reasoning

open import Level

open import List

open import FreeCategory

module Carrier {ℓ} (A : Set ℓ)  where

  data ExpMonoid : Set ℓ where
    Embed : A → ExpMonoid
    MEmpty : ExpMonoid
    _<>_ : ExpMonoid → ExpMonoid → ExpMonoid


  data EquivMonoid : ExpMonoid → ExpMonoid → Set ℓ where
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
                  → EquivMonoid (e₁ <> (e₂ <> e₃)) ((e₁ <> e₂) <> e₃)

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

  open ≈-Reasoning

  mon→list : ExpMonoid → List A
  mon→list (Embed x) =  x ∷ []
  mon→list MEmpty = []
  mon→list (e₁ <> e₂) = mon→list e₁ ++ mon→list e₂

  list→mon : List A → ExpMonoid
  list→mon [] = MEmpty
  list→mon (x ∷ xs) = (Embed x) <> list→mon xs

  resp-<> : ∀ {e e'} → mon→list (e <> e') ≡ mon→list e ++ mon→list e'
  resp-<> = refl

  resp-++ : ∀ {xs ys} → EquivMonoid (list→mon (xs ++ ys)) (list→mon xs <> list→mon ys)
  resp-++ {[]} {ys} =  begin⟨ equiv-setoid ⟩
    list→mon ys
      ≈⟨ equiv-sym left-id-mempty ⟩
    (MEmpty <> list→mon ys) ∎
  resp-++ {x ∷ xs} {ys} = begin⟨ equiv-setoid ⟩
    (Embed x <> list→mon (xs ++ ys))
      ≈⟨ equiv-trans (equiv-cong equiv-refl resp-++) (assoc-mappend (Embed x) (list→mon xs) (list→mon ys)) ⟩
    ((Embed x <> list→mon xs) <> list→mon ys) ∎

  resp-[] : EquivMonoid (list→mon []) MEmpty
  resp-[] = equiv-refl

  list→mon-inv : ∀ {e} → EquivMonoid (list→mon (mon→list e)) e
  list→mon-inv {Embed x} = right-id-mempty
  list→mon-inv {MEmpty} = equiv-refl
  list→mon-inv {e <> e'} = begin⟨ equiv-setoid ⟩
    list→mon (mon→list e ++ mon→list e')
      ≈⟨ resp-++ ⟩
    (list→mon (mon→list e) <> list→mon (mon→list e'))
      ≈⟨ equiv-cong list→mon-inv list→mon-inv ⟩
    (e <> e') ∎

  resp-≡ : ∀ {xs ys} → xs ≡ ys → EquivMonoid (list→mon xs) (list→mon ys)
  resp-≡ {[]} {.[]} refl = equiv-refl
  resp-≡ {x ∷ xs} {.x ∷ .xs} refl = equiv-refl

  module Sound where

    sound : {e e' : ExpMonoid}
          → mon→list e ≡ mon→list e'
          → EquivMonoid e e'
    sound {e} {e'} p = begin⟨ equiv-setoid ⟩
      e                        ≈⟨ equiv-sym list→mon-inv ⟩
      list→mon (mon→list e)  ≈⟨ resp-≡ p ⟩
      list→mon (mon→list e') ≈⟨ list→mon-inv ⟩
      e' ∎

  module Complete where

    complete : {e₁ e₂ : ExpMonoid}
             → EquivMonoid e₁ e₂
             → mon→list e₁ ≡ mon→list e₂
    complete equiv-refl = refl
    complete (equiv-sym p) = sym (complete p)
    complete (equiv-trans p₁ p₂) = trans (complete p₁) (complete p₂)
    complete (equiv-cong p₁ p₂) = cong₂ _++_ (complete p₁) (complete p₂)
    complete left-id-mempty = refl
    complete (right-id-mempty {e}) = right-id-[] (mon→list e)
    complete (assoc-mappend e₁ e₂ e₃) = assoc-++ (mon→list e₁) (mon→list e₂) (mon→list e₃)

module Category {ℓ} {A : Set ℓ} where
  C : A → A → Set ℓ
  C _ _ = A

  open Composition _ C
