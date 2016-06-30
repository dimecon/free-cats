module FreeMonoid where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.SetoidReasoning as ≈-Reasoning

open import List

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
    --open ≈-Reasoning

    sound : {e e' : ExpMonoid}
          → mon→list e ≡ mon→list e'
          → EquivMonoid e e'
    sound {MEmpty} {MEmpty} _ = equiv-refl
    sound {MEmpty} {Embed x} ()
    sound {MEmpty} {e <> e'} prf = begin⟨ equiv-setoid ⟩
      MEmpty
        ≈⟨ equiv-refl ⟩
      list→mon []
        ≈⟨ resp-≡ prf ⟩
      list→mon (mon→list e ++ mon→list e')
        ≈⟨ resp-++ ⟩
      list→mon (mon→list e) <> list→mon (mon→list e')
        ≈⟨ equiv-cong list→mon-inv list→mon-inv ⟩
      (e <> e') ∎
    sound {e <> e'} {Embed x} prf = begin⟨ equiv-setoid ⟩
      (e <> e')
        ≈⟨ equiv-cong (equiv-sym list→mon-inv) (equiv-sym list→mon-inv) ⟩
      (list→mon (mon→list e) <> list→mon (mon→list e'))
        ≈⟨ equiv-sym resp-++ ⟩
      list→mon (mon→list e ++ mon→list e')
        ≈⟨ resp-≡ prf ⟩
      list→mon (x ∷ [])
        ≈⟨ equiv-refl ⟩
      ((Embed x) <> MEmpty)
        ≈⟨ right-id-mempty ⟩
      Embed x ∎
    sound {e₁ <> e₂} {e₁' <> e₂'} prf = begin⟨ equiv-setoid ⟩
      (e₁ <> e₂)
        ≈⟨ equiv-sym list→mon-inv ⟩
      list→mon (mon→list (e₁ <> e₂))
        ≈⟨ resp-≡ refl ⟩
      list→mon (mon→list e₁ ++ mon→list e₂)
        ≈⟨ resp-≡ prf ⟩
      list→mon (mon→list e₁' ++ mon→list e₂')
        ≈⟨ resp-++ ⟩
      (list→mon (mon→list e₁') <> list→mon (mon→list e₂'))
        ≈⟨ equiv-cong list→mon-inv list→mon-inv ⟩
      (e₁' <> e₂') ∎
    sound {e <> e'} {MEmpty} prf = begin⟨ equiv-setoid ⟩
      (e <> e')
        ≈⟨ equiv-cong (equiv-sym list→mon-inv) (equiv-sym list→mon-inv) ⟩
      list→mon (mon→list e) <> list→mon (mon→list e')
        ≈⟨ equiv-sym resp-++ ⟩
      list→mon (mon→list e ++ mon→list e')
        ≈⟨ resp-≡ prf ⟩
      list→mon []
        ≈⟨ equiv-refl ⟩
      MEmpty ∎
    sound {Embed x} {Embed .x} refl = equiv-refl
    sound {Embed x} {MEmpty} ()
    sound {Embed x} {e <> e'} prf = begin⟨ equiv-setoid ⟩
      Embed x
        ≈⟨ equiv-sym right-id-mempty ⟩
      list→mon (x ∷ [])
        ≈⟨ resp-≡ prf ⟩
      list→mon (mon→list e ++ mon→list e')
        ≈⟨ resp-++ ⟩
      (list→mon (mon→list e) <> list→mon (mon→list e'))
        ≈⟨ equiv-cong list→mon-inv list→mon-inv ⟩
      (e <> e') ∎

  module Complete where
    --open ≡-Reasoning

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
