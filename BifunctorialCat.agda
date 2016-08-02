module BifunctorialCat where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.SetoidReasoning as ≈-Reasoning

open import Level

-- type universe
data Ty {ℓ} (A : Set ℓ) : Set ℓ where
  atom : A → Ty A
  _,_  : Ty A → Ty A → Ty A

module Bifunctor {ℓ} (A : Set ℓ) (C : Ty A → Ty A → Set ℓ) where

  data Exp : Ty A → Ty A → Set ℓ where
    embed : ∀ {a a′}
         → C a a′
         → Exp a a′
    id    : ∀ {a}
         → Exp a a
    _<>_   : ∀ {a a′ a′′}
          → Exp a a′ → Exp a′ a′′ → Exp a a′′
    _∥_ : ∀ {a a′ b b′}
      → Exp a a′ → Exp b b′ → Exp (a , b) (a′ , b′)

  data EquivExp : ∀ {a a′} → Exp a a′ → Exp a a′ → Set ℓ where
    equiv-refl : ∀ {a a′} {e : Exp a a′}
              → EquivExp e e
    equiv-sym : ∀ {a a′} {e₁ e₂ : Exp a a′}
             → EquivExp e₁ e₂ → EquivExp e₂ e₁
    equiv-trans : ∀ {a a′} {e₁ e₂ e₃ : Exp a a′}
               → EquivExp e₁ e₂ → EquivExp e₂ e₃ → EquivExp e₁ e₃
    cong-<> : ∀ {a a′ a′′} {f f′ : Exp a a′} {g g′ : Exp a′ a′′}
               → EquivExp f  f′ → EquivExp g  g′
               → EquivExp (f <> g) (f′ <> g′)
    left-id-id : ∀ {a a′} {e : Exp a a′}
              → EquivExp (id <> e) e
    right-id-id : ∀ {a a′} {e : Exp a a′}
               → EquivExp (e <> id) e
    assoc-<> : ∀ {a a′ a′′ a′′′} (e : Exp a a′) (e′ : Exp a′ a′′) (e′′ : Exp a′′ a′′′)
            → EquivExp ((e <> e′) <> e′′) (e <> (e′ <> e′′))
    compat-⊩id : ∀ {a b}
              → EquivExp (id {a} ∥ id {b}) (id {a , b})
    compat-∥-<> : ∀ {a b c} {a′ b′ c′}
              → (f : Exp a b) → (g : Exp b c)
              → (h : Exp a′ b′) → (i : Exp b′ c′)
              → EquivExp ((f <> g) ∥ (h <> i)) ((f ∥ h) <> (g ∥ i))
    cong-∥ : ∀ {a a′ b b′} {f f′ : Exp a a′} {g g′ : Exp b b′}
          → EquivExp f f′ → EquivExp g g′ → EquivExp (f ∥ g) (f′ ∥ g′)

  equiv-setoid : {a a′ : Ty A} → Setoid _ _
  equiv-setoid {a} {a′} = record
    { Carrier = Exp a a′
    ; _≈_ = EquivExp
    ; isEquivalence = record
      { refl  = equiv-refl
      ; sym   = equiv-sym
      ; trans = equiv-trans
      }
    }

  data FreeBiCat : Ty A → Ty A → Set ℓ where
    nil-atom : ∀ {a} → FreeBiCat (atom a) (atom a)
    nil-pair : ∀ {a a′ b b′}
            → FreeBiCat a a′ → FreeBiCat b b′ → FreeBiCat (a , b) (a′ , b′)
    cons-atom : ∀ {a a′ a′′}
             → C (atom a) a′ → FreeBiCat a′ a′′ → FreeBiCat (atom a) a′′
    cons-pair : ∀ {a a′ b b′ c c′}
             → FreeBiCat a a′ → FreeBiCat b b′ → C (a′ , b′) c → FreeBiCat c c′ → FreeBiCat (a , b) c′

  module _ where
    open ≈-Reasoning

    nil : ∀ {a} → FreeBiCat a a
    nil {atom _} = nil-atom
    nil {_ , _} = nil-pair nil nil

    _∷_ : ∀ {a a′ a′′} → C a a′ → FreeBiCat a′ a′′ → FreeBiCat a a′′
    _∷_ {atom m} x xs = cons-atom x xs
    _∷_ {a₁ , a₂} x xs = cons-pair nil nil x xs

    _++_ : ∀ {a a′ a′′} → FreeBiCat a a′ → FreeBiCat a′ a′′ → FreeBiCat a a′′
    nil-atom ++ y = y
    nil-pair f g ++ nil-pair h i = nil-pair (f ++ h) (g ++ i)
    nil-pair f g ++ cons-pair h i j k = cons-pair (f ++ h) (g ++ i) j k
    cons-atom f g ++ h = cons-atom f (g ++ h)
    cons-pair f g h i ++ j = cons-pair f g h (i ++ j)

    left-id-nil : ∀ {a a′} {f : FreeBiCat a a′} → nil ++ f ≡ f
    left-id-nil {f = nil-atom} = refl
    left-id-nil {f = nil-pair f g} = cong₂ nil-pair left-id-nil left-id-nil
    left-id-nil {f = cons-atom u f} = refl
    left-id-nil {f = cons-pair f g u h} = cong₂ (λ p q → cons-pair p q u h) left-id-nil left-id-nil

    right-id-nil : ∀ {a a′} {f : FreeBiCat a a′} → f ++ nil ≡ f
    right-id-nil {f = nil-atom} = refl
    right-id-nil {f = nil-pair f g} = cong₂ nil-pair right-id-nil right-id-nil
    right-id-nil {f = cons-atom u f} = cong (cons-atom u) right-id-nil
    right-id-nil {f = cons-pair f g u h} = cong (cons-pair f g u) right-id-nil

    assoc-++ : ∀ {a a′ a′′ a′′′} (f : FreeBiCat a a′) (g : FreeBiCat a′ a′′) (h : FreeBiCat a′′ a′′′)
            → (f ++ g) ++ h ≡ f ++ (g ++ h)
    assoc-++ nil-atom _ _ = refl
    assoc-++ (nil-pair f g) (nil-pair h i) (nil-pair j k) =
      cong₂ nil-pair (assoc-++ f h j) (assoc-++ g i k)
    assoc-++ (nil-pair f g) (nil-pair h i) (cons-pair j k l m) =
      cong₂ (λ p q → cons-pair p q l m) (assoc-++ f h j) (assoc-++ g i k)
    assoc-++ (nil-pair f g) (cons-pair h i j k) l = refl
    assoc-++ (cons-atom x f) g h = cong (λ p → cons-atom x p) (assoc-++ f g h)
    assoc-++ (cons-pair f g u h) i j = cong (λ p → cons-pair f g u p) (assoc-++ h i j)

    exp→free : ∀ {a a′} → Exp a a′ → FreeBiCat a a′
    exp→free (embed f) = f ∷ nil
    exp→free id = nil
    exp→free (f <> g) = exp→free f ++ exp→free g
    exp→free (f ∥ g) = nil-pair (exp→free f) (exp→free g)

    free→exp : ∀ {a a′} → FreeBiCat a a′ → Exp a a′
    free→exp nil-atom = id
    free→exp (nil-pair f g) = free→exp f ∥ free→exp g
    free→exp (cons-atom u f) = embed u <> free→exp f
    free→exp (cons-pair f g u h) = (free→exp f ∥ free→exp g) <> (embed u <> free→exp h)

    resp-nil : ∀ {a} → EquivExp (free→exp (nil {a})) id
    resp-nil {atom _} = equiv-refl
    resp-nil {a , b} = begin⟨ equiv-setoid ⟩
      (free→exp nil ∥ free→exp nil) ≈⟨ cong-∥ resp-nil resp-nil ⟩
      (id ∥ id) ≈⟨ compat-⊩id ⟩
      id ∎

    resp-∷ : ∀ {a a′ a′′} {x : C a a′} {xs : FreeBiCat a′ a′′} →  EquivExp (free→exp (x ∷ xs)) (embed x <> free→exp xs)
    resp-∷ {atom m} = equiv-refl
    resp-∷ {a , b} {x = x} {xs = xs} = begin⟨ equiv-setoid ⟩
      (free→exp nil ∥ free→exp nil) <> (embed x <> free→exp xs) ≈⟨ cong-<> (cong-∥ resp-nil resp-nil) equiv-refl ⟩
      (id ∥ id) <> (embed x <> free→exp xs) ≈⟨ cong-<> compat-⊩id equiv-refl ⟩
      id <> (embed x <> free→exp xs) ≈⟨ left-id-id ⟩
      embed x <> free→exp xs ∎

    resp-++ : ∀ {a a′ a′′} (f : FreeBiCat a a′) (g : FreeBiCat a′ a′′)
           → EquivExp (free→exp (f ++ g)) (free→exp f <> free→exp g)
    resp-++ nil-atom _ = equiv-sym left-id-id
    resp-++ (nil-pair f g) (nil-pair h i) = equiv-trans (cong-∥ (resp-++ f h) (resp-++ g i))
                                                  (compat-∥-<> (free→exp f) (free→exp h) (free→exp g) (free→exp i))
    resp-++ (nil-pair f g) (cons-pair h i u j) = begin⟨ equiv-setoid ⟩
      (free→exp (f ++ h) ∥ free→exp (g ++ i)) <> (embed u <> free→exp j)
        ≈⟨ cong-<> (cong-∥ (resp-++ f h) (resp-++ g i)) equiv-refl ⟩
      ((free→exp f <> free→exp h) ∥ (free→exp g <> free→exp i)) <> (embed u <> free→exp j)
        ≈⟨ cong-<> (compat-∥-<> (free→exp f) (free→exp h) (free→exp g) (free→exp i)) equiv-refl ⟩
      ((free→exp f ∥ free→exp g) <> (free→exp h ∥ free→exp i)) <> (embed u <> free→exp j)
        ≈⟨ assoc-<> (free→exp f ∥ free→exp g) (free→exp h ∥ free→exp i) (embed u <> free→exp j) ⟩
      (free→exp f ∥ free→exp g) <> ((free→exp h ∥ free→exp i) <> (embed u <> free→exp j)) ∎
    resp-++ (cons-atom x xs) ys = begin⟨ equiv-setoid ⟩
      embed x <> free→exp (xs ++ ys)
        ≈⟨ cong-<> equiv-refl (resp-++ xs ys) ⟩
      embed x <> (free→exp xs <> free→exp ys)
        ≈⟨ equiv-sym (assoc-<> (embed x) (free→exp xs) (free→exp ys)) ⟩
      (embed x <> free→exp xs) <> free→exp ys ∎
    resp-++ (cons-pair f h u i) g = begin⟨ equiv-setoid ⟩
      (free→exp f ∥ free→exp h) <> (embed u <> free→exp (i ++ g))
        ≈⟨ equiv-sym (assoc-<> (free→exp f ∥ free→exp h) (embed u) (free→exp (i ++ g))) ⟩
      ((free→exp f ∥ free→exp h) <> embed u) <> (free→exp (i ++ g))
        ≈⟨ cong-<> equiv-refl (resp-++ i g) ⟩
      ((free→exp f ∥ free→exp h) <> embed u) <> (free→exp i <> free→exp g)
        ≈⟨ equiv-sym (assoc-<> ((free→exp f ∥ free→exp h) <> embed u) (free→exp i) (free→exp g)) ⟩
      (((free→exp f ∥ free→exp h) <> embed u) <> free→exp i) <> free→exp g
        ≈⟨ cong-<> (assoc-<> (free→exp f ∥ free→exp h) (embed u) (free→exp i)) equiv-refl ⟩
      ((free→exp f ∥ free→exp h) <> (embed u <> free→exp i)) <> free→exp g
        ≈⟨ assoc-<> (free→exp f ∥ free→exp h) (embed u <> free→exp i) (free→exp g) ⟩
      (free→exp f ∥ free→exp h) <> ((embed u <> free→exp i) <> free→exp g)
        ≈⟨ equiv-sym (assoc-<> (free→exp f ∥ free→exp h) (embed u <> free→exp i) (free→exp g)) ⟩
      ((free→exp f ∥ free→exp h) <> (embed u <> free→exp i)) <> free→exp g ∎

    free→exp-exp→free : ∀ {a a′} (e : Exp a a′) → EquivExp (free→exp (exp→free e)) e
    free→exp-exp→free (embed u) = begin⟨ equiv-setoid ⟩
      free→exp (u ∷ nil) ≈⟨ resp-∷ ⟩
      embed u <> free→exp nil ≈⟨ cong-<> equiv-refl resp-nil ⟩
      embed u <> id ≈⟨ right-id-id ⟩
      embed u ∎
    free→exp-exp→free id = resp-nil
    free→exp-exp→free (f <> g) = begin⟨ equiv-setoid ⟩
      free→exp (exp→free f ++ exp→free g) ≈⟨ resp-++ (exp→free f) (exp→free g) ⟩
      (free→exp (exp→free f) <> free→exp (exp→free g)) ≈⟨ cong-<> (free→exp-exp→free f) (free→exp-exp→free g) ⟩
      (f <> g) ∎
    free→exp-exp→free (f ∥ g) = cong-∥ (free→exp-exp→free f) (free→exp-exp→free g)

  resp-≡ : ∀ {a a′} {f g : FreeBiCat a a′} → f ≡ g → EquivExp (free→exp f) (free→exp g)
  resp-≡ refl = equiv-refl

  module Sound where
    open ≈-Reasoning

    sound : ∀ {a a′} {e e′ : Exp a a′}
         → exp→free e ≡ exp→free e′
         → EquivExp e e′
    sound {e = e} {e′ = e′} p = begin⟨ equiv-setoid ⟩
      e ≈⟨ equiv-sym (free→exp-exp→free e) ⟩
      free→exp (exp→free e) ≈⟨ resp-≡ p ⟩
      free→exp (exp→free e′) ≈⟨ free→exp-exp→free e′ ⟩
      e′ ∎

  module Complete where
    open ≡-Reasoning

    complete : ∀ {a a′} {e₁ e₂ : Exp a a′}
            → EquivExp e₁ e₂ → exp→free e₁ ≡ exp→free e₂
    complete equiv-refl = refl
    complete (equiv-sym x) = sym (complete x)
    complete (equiv-trans p q) = trans (complete p) (complete q)
    complete (cong-<> p q) = cong₂ _++_ (complete p) (complete q)
    complete left-id-id = left-id-nil
    complete right-id-id = right-id-nil
    complete (assoc-<> f g h) = assoc-++ (exp→free f) (exp→free g) (exp→free h)
    complete compat-⊩id = refl
    complete (compat-∥-<> f g h i) = refl
    complete (cong-∥ p q) = cong₂ nil-pair (complete p) (complete q)
