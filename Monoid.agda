open import Relation.Binary.PropositionalEquality
open import Level

record Monoid {n} : Set (suc n) where
  field
    A : Set n
    
    mempty : A
    _<>_   : A → A → A

    left-id-mempty  : ∀ a → mempty <> a ≡ a
    right-id-mempty : ∀ a → a <> mempty ≡ a
    assoc-<> : ∀ a₁ a₂ a₃ → a₁ <> (a₂ <> a₃) ≡ (a₁ <> a₂) <> a₃

-- Prove List is a monoid
infixr 5 _∷_
data List (A : Set) : Set where
  nil : List A
  _∷_ : (a : A) → List A → List A

infixr 4 _++_
_++_ : ∀ {A} → List A → List A → List A
_++_ nil      ys = ys
_++_ (x ∷ xs) ys = x ∷ (xs ++ ys)

left-id-nil : ∀ {A} → (ys : List A)
            → nil ++ ys ≡ ys
left-id-nil ys = refl

right-id-nil : ∀ {A} → (xs : List A)
             → xs ++ nil ≡ xs
right-id-nil nil = refl
right-id-nil (x ∷ xs) = cong (λ xs' → x ∷ xs') (right-id-nil xs)

assoc-++ : ∀{A} → (xs ys zs : List A)
         → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ nil ys zs = refl
assoc-++ (x ∷ xs) ys zs = cong (λ xs' → x ∷ xs') (assoc-++ xs ys zs)

List-Monoid : Set → Monoid
List-Monoid A = record
  { A = List A
  ; mempty = nil
  ; _<>_ = _++_
  ; left-id-mempty  = left-id-nil
  ; right-id-mempty = right-id-nil
  ; assoc-<> = assoc-++
  }

record MonoidHom (M M' : Monoid) : Set where
  open Monoid M
  open Monoid M' renaming ( A to A'
                          ; mempty to mempty'
                          ; _<>_ to _<>'_
                          ; left-id-mempty to left-id-mempty'
                          ; right-id-mempty to right-id-mempty'
                          ; assoc-<> to assoc-<>'
                          )

  field
    f : A → A'
    respect-mempty : f mempty ≡ mempty'
    respect-<>     : (x y : A)
                   → f (x <> y) ≡ (f x) <>' (f y)
