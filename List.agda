module List where

open import Relation.Binary.PropositionalEquality

open import Data.List public
open import Data.List.Properties public

open import Level

--record Monoid {n} : Set (suc n) where
--  field
--    A : Set n
--
--    mempty : A
--    _<>_   : A → A → A
--
--    left-id-mempty  : ∀ a → mempty <> a ≡ a
--    right-id-mempty : ∀ a → a <> mempty ≡ a
--    assoc-<> : ∀ a₁ a₂ a₃ → a₁ <> (a₂ <> a₃) ≡ (a₁ <> a₂) <> a₃

module _ {ℓ} {A : Set ℓ} where

  left-id-[] : (ys : List A) → [] ++ ys ≡ ys
  left-id-[] ys = refl

  right-id-[] :(xs : List A) → xs ++ [] ≡ xs
  right-id-[] [] = refl
  right-id-[] (x ∷ xs) = cong (λ xs' → x ∷ xs') (right-id-[] xs)

  assoc-++ : (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
  assoc-++ [] ys zs = refl
  assoc-++ (x ∷ xs) ys zs = cong (λ xs' → x ∷ xs') (assoc-++ xs ys zs)

--  left-is-[] : (xs ys : List A) → xs ++ ys ≡ [] → xs ≡ []
--  left-is-[] [] ys _ = refl
--  left-is-[] (x ∷ xs) ys prf = cong (_++_ {!!}) (left-is-[] xs ys {!!})

--List-Monoid : Set → Monoid
--List-Monoid A = record
--  { A = List A
--  ; mempty = []
--  ; _<>_ = _++_
--  ; left-id-mempty  = left-id-[]
--  ; right-id-mempty = right-id-[]
--  ; assoc-<> = assoc-++
--  }
--
--record MonoidHom (M M' : Monoid) : Set where
--  open Monoid M
--  open Monoid M' renaming ( A to A'
--                          ; mempty to mempty'
--                          ; _<>_ to _<>'_
--                          ; left-id-mempty to left-id-mempty'
--                          ; right-id-mempty to right-id-mempty'
--                          ; assoc-<> to assoc-<>'
--                          )
--
--  field
--    f : A → A'
--    respect-mempty : f mempty ≡ mempty'
--    respect-<>     : ∀ {x y}
--                   → f (x <> y) ≡ (f x) <>' (f y)

--module _ where
--  --open Monoid
--
--  forget : Monoid → Set
--  forget = Monoid.A
--
--  free : Set → Monoid
--  free A = record
--    { A = List A
--    ; mempty = nil
--    ; _<>_ = _++_
--    ; left-id-mempty  = left-id-nil
--    ; right-id-mempty = right-id-nil
--    ; assoc-<> = assoc-++
--    }
--
--  record _⊣_ (F : Set → Monoid) (G : Monoid → Set) : Set₁ where
--    field
--      toSet : {A : Set}
--            → {M : Monoid}
--            → MonoidHom (F A) M
--            → (A → G M)
--      toMonoid : {A : Set}
--               → {M : Monoid}
--               → (A → G M)
--               → MonoidHom (F A) M
--
--      -- and probably something to prove that toSet and toMonoid are
--      -- inverses of each other?
--
--  foldr : {A B : Set} → (A → B → B) → B → List A → B
--  foldr f b nil = b
--  foldr f b (x ∷ xs) = f x (foldr f b xs)
--
--  fold-map : {A : Set} → (M : Monoid) → (A → forget M) → List A → (forget M)
--  fold-map M f = foldr (λ x r → (Monoid._<>_ M) (f x) r) (Monoid.mempty M)
--
--  free⊣forget-toSet : {A : Set} {M : Monoid}
--                    → MonoidHom (free A) M → (A → forget M)
--  free⊣forget-toSet φ = λ a → MonoidHom.f φ (a ∷ nil)
--
--  respect-<> : ∀ {A}{M} → (g : A → forget M) → (x y : Monoid.A (free A))
--             → fold-map M g (Monoid._<>_ (free A) x y) ≡ Monoid._<>_ M (fold-map M g x) (fold-map M g y)
--  respect-<> g nil y     = {!!}
--  respect-<> g (a ∷ x) y = {!!}
--
--  free⊣forget-toMonoid : {A : Set} {M : Monoid}
--                       → (A → forget M) → MonoidHom (free A) M
--  free⊣forget-toMonoid {_} {M} g = let f = fold-map M g in record
--    { f = f
--    ; respect-mempty = refl
--    ; respect-<> = {! !}
--    }
--
--  free⊣forget : free ⊣ forget
--  free⊣forget = record
--    { toSet = free⊣forget-toSet
--    ; toMonoid = free⊣forget-toMonoid
--    }
