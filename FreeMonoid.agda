module FreeMonoid where

open import Monoid
open import Relation.Binary.PropositionalEquality


data ExpMonoid (A : Set) : Set where
  Embed : A → ExpMonoid A
  MEmpty : ExpMonoid A
  MAppend : ExpMonoid A → ExpMonoid A → ExpMonoid A

data EquivMonoid {A : Set} : ExpMonoid A → ExpMonoid A → Set where
  equiv-refl : {e : ExpMonoid A}
             → EquivMonoid e e
  equiv-sym : {e1 e2 : ExpMonoid A}
            → EquivMonoid e1 e2 → EquivMonoid e2 e1
  equiv-trans : {e1 e2 e3 : ExpMonoid A}
              → EquivMonoid e1 e2
              → EquivMonoid e2 e3
              → EquivMonoid e1 e3
  left-id-mempty : {e : ExpMonoid A}
                 → EquivMonoid (MAppend MEmpty e) e
  right-id-mempty : {e : ExpMonoid A}
                  → EquivMonoid (MAppend e MEmpty) e
  assoc-mappend : {e1 e2 e3 : ExpMonoid A}
                → EquivMonoid (MAppend (MAppend e1 e2) e3) (MAppend e1 (MAppend e2 e3))

eqClass : {A : Set} → ExpMonoid A → List A
eqClass = {!!}

sound : {A : Set}
      → {e1 e2 : ExpMonoid A}
      → eqClass e1 ≡ eqClass e2
      → EquivMonoid e1 e2
sound = {!!}

complete : {A : Set}
         → {e1 e2 : ExpMonoid A}
         → EquivMonoid e1 e2
         → eqClass e1 ≡ eqClass e2
complete = {!!}
