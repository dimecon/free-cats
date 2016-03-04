open import Relation.Binary.PropositionalEquality
open import Function using (_∘_; _$_)

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
    respect-<>     : {x y : A}
                   → f (x <> y) ≡ (f x) <>' (f y)

forget : Monoid → Set
forget = Monoid.A

free : Set → Monoid
free A = record
  { A = List A
  ; mempty = nil
  ; _<>_ = _++_
  ; left-id-mempty  = left-id-nil
  ; right-id-mempty = right-id-nil
  ; assoc-<> = assoc-++
  }
                   
record _⊣_ (F : Set → Monoid) (G : Monoid → Set) : Set₁ where
  field
    toSet : {A : Set}
          → {M : Monoid}
          → MonoidHom (F A) M
          → (A → G M)
    toMonoid : {A : Set}
             → {M : Monoid}
             → (A → G M)
             → MonoidHom (F A) M

    -- and probably something to prove that toSet and toMonoid are
    -- inverses of each other?
    -- yeah, I'm looking into this

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f b nil = b
foldr f b (x ∷ xs) = f x (foldr f b xs)

fold-map : {A : Set} → (M : Monoid) → (A → forget M) → List A → (forget M)
fold-map M f = foldr (λ x r → (Monoid._<>_ M) (f x) r) (Monoid.mempty M)

free⊣forget-toSet : {A : Set} {M : Monoid}
                  → MonoidHom (free A) M → (A → forget M)
free⊣forget-toSet φ = λ a → MonoidHom.f φ (a ∷ nil)

free⊣forget-toMonoid : {A : Set} {M : Monoid}
                     → (A → forget M) → MonoidHom (free A) M
free⊣forget-toMonoid {_} {M} g = record
  { f = f
  ; respect-mempty = refl
  ; respect-<> = {!!}
  }
  where
    f = fold-map M g
    
    respect-<> : {A : Set} {xs ys : List A} → f (xs ++ ys) ≡ (f xs) (Monoid._<>_ M) (f ys)
    respect-<> x y = ?
                     
free⊣forget : free ⊣ forget
free⊣forget = record
  { toSet = free⊣forget-toSet
  ; toMonoid = free⊣forget-toMonoid
  }
