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
    id    : ∀ a
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
              → EquivExp (id a <> e) e
    right-id-id : ∀ {a a′} {e : Exp a a′}
               → EquivExp (e <> id a′) e
    assoc-<> : ∀ {a a′ a′′ a′′′} (e : Exp a a′) (e′ : Exp a′ a′′) (e′′ : Exp a′′ a′′′)
            → EquivExp ((e <> e′) <> e′′) (e <> (e′ <> e′′))
    compat-⊩id : ∀ {a b}
              → EquivExp (id a ∥ id b) (id (a , b))
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

    _++_ : ∀ {a a′ a′′} → FreeBiCat a a′ → FreeBiCat a′ a′′ → FreeBiCat a a′′
    nil-atom ++ y = y
    nil-pair f g ++ nil-pair h i = nil-pair (f ++ h) (g ++ i)
    nil-pair f g ++ cons-pair h i j k = cons-pair (f ++ h) (g ++ i) j k
    cons-atom f g ++ h = cons-atom f (g ++ h)
    cons-pair f g h i ++ j = cons-pair f g h (i ++ j)

    left-id-nil-pair : ∀ {a b c} (f : FreeBiCat a a) (g : FreeBiCat b b) (h : FreeBiCat (a , b) c ) → (nil-pair f g ++ h) ≡ h
    left-id-nil-pair f g h = {!f!}

    right-id-nil-atom : ∀ {a a′} (f : FreeBiCat a (atom a′)) → f ++ nil-atom ≡ f
    right-id-nil-atom nil-atom = refl
    right-id-nil-atom (cons-atom u f) = cong (λ x → cons-atom u x) (right-id-nil-atom f)
    right-id-nil-atom (cons-pair f g u h) = cong (λ x → cons-pair f g u x) (right-id-nil-atom h)

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
    exp→free {atom _} {atom _ } (embed f) = cons-atom f nil-atom
    exp→free {atom _} {a , b  } (embed f) = cons-atom f (nil-pair (exp→free (id a)) (exp→free (id b)))
    exp→free {a , b } {atom _ } (embed f) = cons-pair (exp→free (id a)) (exp→free (id b)) f nil-atom
    exp→free {a , b } {a′ , b′ } (embed f) = cons-pair (exp→free (id a)) (exp→free (id b)) f (nil-pair (exp→free (id a′)) (exp→free (id b′)))
    exp→free (id {atom _}) = nil-atom
    exp→free (id {a , b}) = nil-pair (exp→free (id a)) (exp→free (id b))
    exp→free {a} {a′} (_<>_ {a′ = b} f g) = exp→free {a} {b} f ++ exp→free {b} {a′} g
    exp→free (f ∥ g) = nil-pair (exp→free f) (exp→free g)

    resp-<> : ∀ {a b c} {f : Exp a b} {g : Exp b c} → exp→free (f <> g) ≡ exp→free f ++ exp→free g
    resp-<> = {!!}

    free→exp : ∀ {a a′} → FreeBiCat a a′ → Exp a a′
    free→exp nil-atom = id _
    free→exp (nil-pair f g) = free→exp f ∥ free→exp g
    free→exp (cons-atom u f) = embed u <> free→exp f
    free→exp (cons-pair f g u h) = (free→exp f ∥ free→exp g) <> (embed u <> free→exp h)

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
    free→exp-exp→free {atom m} {atom k} (embed u) = right-id-id
    free→exp-exp→free {atom m} {a , b} (embed u) = {!free→exp (exp→free (id a)) ∥ free→exp (exp→free (id b))!}
    free→exp-exp→free {a , b} {atom m} (embed u) = {!!}
    free→exp-exp→free {a , b} {a′ , b′} (embed u) = {!!}
    free→exp-exp→free (id a) = {!!}
    -- Why do I need to specify the implicit cases {atom x} {atom k} and {atom x} {a , b} if the proofs are the same?
    -- Doing {atom x} {_} or {atom x} or {atom x} {a′} doesn't work
    free→exp-exp→free {atom x} {atom y} (f <> g) = begin⟨ equiv-setoid ⟩
      free→exp (exp→free f ++ exp→free g) ≈⟨ resp-++ (exp→free f) (exp→free g) ⟩
      (free→exp (exp→free f) <> free→exp (exp→free g)) ≈⟨ cong-<> (free→exp-exp→free f) (free→exp-exp→free g) ⟩
      (f <> g) ∎
    free→exp-exp→free {atom x} {a , b} (f <> g) = begin⟨ equiv-setoid ⟩
      free→exp (exp→free f ++ exp→free g) ≈⟨ resp-++ (exp→free f) (exp→free g) ⟩
      (free→exp (exp→free f) <> free→exp (exp→free g)) ≈⟨ cong-<> (free→exp-exp→free f) (free→exp-exp→free g) ⟩
      (f <> g) ∎
    free→exp-exp→free {a , b} {atom x} (f <> g) = begin⟨ equiv-setoid ⟩
      free→exp (exp→free f ++ exp→free g) ≈⟨ resp-++ (exp→free f) (exp→free g) ⟩
      (free→exp (exp→free f) <> free→exp (exp→free g)) ≈⟨ cong-<> (free→exp-exp→free f) (free→exp-exp→free g) ⟩
      (f <> g) ∎
    free→exp-exp→free {a , b} {a′ , b′} (f <> g) = begin⟨ equiv-setoid ⟩
      free→exp (exp→free f ++ exp→free g) ≈⟨ resp-++ (exp→free f) (exp→free g) ⟩
      (free→exp (exp→free f) <> free→exp (exp→free g)) ≈⟨ cong-<> (free→exp-exp→free f) (free→exp-exp→free g) ⟩
      (f <> g) ∎
    free→exp-exp→free (f ∥ g) = cong-∥ (free→exp-exp→free f) (free→exp-exp→free g)

  module Sound where
    sound : ∀ {a a′} {e e′ : Exp a a′}
         → exp→free e ≡ exp→free e′
         → EquivExp e e′
    sound = {!!}
    --sound {e = e} {e′ = e′} p = begin⟨ equiv-setoid ⟩
    --  e                        ≈⟨ equiv-sym free→exp-inv ⟩
    --  free→exp (exp→free e)  ≈⟨ resp-≡ p ⟩
    --  free→exp (exp→free e′) ≈⟨ free→exp-inv ⟩
    --  e′ ∎

  module Complete where
    open ≡-Reasoning

    complete : ∀ {a a′}
            → {e₁ e₂ : Exp a a′}
            → EquivExp e₁ e₂
            → exp→free e₁ ≡ exp→free e₂
    complete equiv-refl = refl
    complete (equiv-sym x) = sym (complete x)
    complete (equiv-trans p q) = trans (complete p) (complete q)
    complete {a} {a′} {e₁ = f <> g} {e₂ = f′ <> g′} (cong-<> {.a} {a′ = b} p q) = {!!}
--      cong₂ {A = FreeBiCat a b} {B = FreeBiCat b a′} {!!} (complete p) (complete q)
    complete {atom m} {atom x} left-id-id = refl
    complete {atom m} {a , b} left-id-id = refl
    complete {atom x , atom y} {atom z} {e₂ = f} left-id-id with exp→free f
    complete {atom x , atom y} {atom z} {e₂ = f} left-id-id | cons-pair _ _ _ _ = refl
    complete {(a , b) , atom x} {atom m} {e₂ = f} left-id-id with exp→free f
    --complete {(a , b) , atom x} {atom m} left-id-id | cons-pair f g u h = cong (λ x → cons-pair {!x!} g u h) (complete left-id-id)
    complete {(a , b) , atom x} {atom m} left-id-id | cons-pair f g u h = {!!}
    complete {a , (b , c)} {atom m} {e₂ = f} left-id-id with exp→free f
    complete {a , (b , c)} {atom m} left-id-id | cons-pair _ _ _ _ = {!!}
    complete {a , b} {a′ , b′} {e₂ = f} left-id-id with exp→free f
    complete {a , b} {a′ , b′} left-id-id | nil-pair _ _ = {!!}
    complete {a , b} {a′ , b′} left-id-id | cons-pair _ _ _ _ = {!!}
    complete {a′ = atom x} {e₂ = f} right-id-id = begin
      exp→free (f <> (id (atom x))) ≡⟨ {!resp-++!} ⟩
      exp→free f ++ exp→free (id (atom x)) ≡⟨ {!!} ⟩
      exp→free f ∎
    complete {a′ = a′ , a′₁} right-id-id = {!!}
    complete (assoc-<> f g h) = {!!}
    complete compat-⊩id = refl
    complete (compat-∥-<> f g h i) = {!!}
    complete (cong-∥ f g) = {!!}
  --  complete (equiv-cong p₁ p₂) = cong₂ _++_ (complete p₁) (complete p₂)
  --  complete left-id-id = refl
  --  complete right-id-id = right-id-nil
  --  complete (assoc-<> e₁ e₂ e₃) = assoc-++ (exp→free e₁) (exp→free e₂) (exp→free e₃)
