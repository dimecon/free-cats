module AssociativeCat where

open import Data.List hiding (all)
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.SetoidReasoning as ≈-Reasoning

-- type universe
data Ty (A : Set) : Set where
  atom : A → Ty A
  _,_  : Ty A → Ty A → Ty A

module Associative (A : Set) (C : Ty A → Ty A → Set) where
  Type : Set
  Type = Ty A

  data Exp : Type → Type → Set where
    embed : ∀ {a a′}
          → C a a′
          → Exp a a′
    id    : ∀ {a}
          → Exp a a
    _<>_  : ∀ {a a′ a′′}
          → Exp a a′ → Exp a′ a′′ → Exp a a′′
    _∥_   : ∀ {a a′ b b′}
          → Exp a a′ → Exp b b′ → Exp (a , b) (a′ , b′)
    associate : ∀ {a b c}
              → Exp ((a , b) , c) (a , (b , c))
    disassociate : ∀ {a b c}
                 → Exp (a , (b , c)) ((a , b) , c)

  data Rearranging : Type → Type → Set where
    id′   : ∀ {a}
          → Rearranging a a
    _<>′_ : ∀ {a a′ a′′}
          → Rearranging a a′ → Rearranging a′ a′′ → Rearranging a a′′
    _∥′_  : ∀ {a a′ b b′}
          → Rearranging a a′ → Rearranging b b′ → Rearranging (a , b) (a′ , b′)
    associate′ : ∀ {a b c}
               → Rearranging ((a , b) , c) (a , (b , c))
    disassociate′ : ∀ {a b c}
                  → Rearranging (a , (b , c)) ((a , b) , c)

  rearranging→exp : ∀ {a a′} → Rearranging a a′ → Exp a a′
  rearranging→exp id′ = id
  rearranging→exp (f <>′ g) = rearranging→exp f <> rearranging→exp g
  rearranging→exp (f ∥′ g) = rearranging→exp f ∥ rearranging→exp g
  rearranging→exp associate′ = associate
  rearranging→exp disassociate′ = disassociate

  data _≈_ : ∀ {a a′} → Exp a a′ → Exp a a′ → Set where
    equiv-refl : ∀ {a a′} {e : Exp a a′}
              → e ≈ e
    equiv-sym : ∀ {a a′} {e₁ e₂ : Exp a a′}
             → e₁ ≈ e₂ → e₂ ≈ e₁
    equiv-trans : ∀ {a a′} {e₁ e₂ e₃ : Exp a a′}
               → e₁ ≈ e₂ → e₂ ≈ e₃ → e₁ ≈ e₃
    cong-<> : ∀ {a a′ a′′} {f f′ : Exp a a′} {g g′ : Exp a′ a′′}
               → f  ≈ f′ → g  ≈ g′
               → (f <> g) ≈ (f′ <> g′)
    left-id-id : ∀ {a a′} {e : Exp a a′}
              → (id <> e) ≈ e
    right-id-id : ∀ {a a′} {e : Exp a a′}
               → (e <> id) ≈ e
    assoc-<> : ∀ {a a′ a′′ a′′′} (e : Exp a a′) (e′ : Exp a′ a′′) (e′′ : Exp a′′ a′′′)
            → ((e <> e′) <> e′′) ≈ (e <> (e′ <> e′′))
    compat-∥-<> : ∀ {a b c} {a′ b′ c′}
                → (f : Exp a b) → (g : Exp b c)
                → (h : Exp a′ b′) → (i : Exp b′ c′)
                → ((f <> g) ∥ (h <> i)) ≈ ((f ∥ h) <> (g ∥ i))
    cong-∥ : ∀ {a a′ b b′} {f f′ : Exp a a′} {g g′ : Exp b b′}
           → f ≈ f′ → g ≈ g′ → (f ∥ g) ≈ (f′ ∥ g′)
    rearranging : ∀ {a a′}
                → (r₁ r₂ : Rearranging a a′)
                → rearranging→exp r₁ ≈ rearranging→exp r₂

  equiv-setoid : {a a′ : Type} → Setoid _ _
  equiv-setoid {a} {a′} = record
    { Carrier = Exp a a′
    ; _≈_ = _≈_
    ; isEquivalence = record
      { refl  = equiv-refl
      ; sym   = equiv-sym
      ; trans = equiv-trans
      }
    }

  ty→list : ∀ {X} → Ty X → List X
  ty→list (atom x) = x ∷ []
  ty→list (t₁ , t₂) = ty→list t₁ ++ ty→list t₂

  data Solidity : Set where
    Solid : Solidity
    Blank : Solidity

  data SolidityList : List A → Set where
    []  : SolidityList []
    _∷_ : ∀ {a as} → Solidity → SolidityList as → SolidityList (a ∷ as)

  _++′_ : ∀ {as₁ as₂} → SolidityList as₁ → SolidityList as₂ → SolidityList (as₁ ++ as₂)
  [] ++′ ss = ss
  (s ∷ ss₁) ++′ ss₂ = s ∷ (ss₁ ++′ ss₂)

  all : Solidity → (as : List A) → SolidityList as
  all _ [] = []
  all s (a ∷ as) = s ∷ all s as

  data SomeSolid : ∀ {as} → SolidityList as → Set where
    here  : ∀ {a as ss}
          → SomeSolid {a ∷ as} (Solid ∷ ss)
    there : ∀ {a as ss}
          → SomeSolid {as} ss
          → SomeSolid {a ∷ as} (Blank ∷ ss)

  data Row : ∀ {as as′} → SolidityList as → SolidityList as′ → Set where
    []    : ∀ {as ss}
          → Row {as} ss (all Blank as)
    blank : ∀ {a as as′ ss ss′}
          → Row {as} {as′} ss ss′
          → Row {a ∷ as} {a ∷ as′} (Blank ∷ ss) (Blank ∷ ss′)
    piece : ∀ {t t′}
          → C t t′
          → let as₀  = ty→list t
                as₀′ = ty→list t′
         in {ss₀ : SolidityList as₀}
          → SomeSolid ss₀
          → let ss₀′ = all Solid as₀′
         in ∀ {as as′ ss ss′}
          → Row {as} {as′} ss ss′
          → Row {as₀ ++ as} {as₀′ ++ as′} (ss₀ ++′ ss) (ss₀′ ++′ ss′)

  data Pile : ∀ {as as′} → SolidityList as → SolidityList as′ → Set where
    [] : ∀ {as ss}
       → Pile {as} ss (all Blank as)
    _∷_ : ∀ {as as′ as′′ ss ss′ ss′′}
        → Row {as} {as′} ss ss′
        → Pile {as′} {as′′} ss′ ss′′
        → Pile {as} {as′′} ss ss′′

  data FreeAssocCat (t t′ : Type) : Set where
    MkFreeAssocCat : let as  = ty→list t
                         as′ = ty→list t′
                         ss  = all Solid as
                         ss′ = all Blank as′
                  in Pile ss ss′
                   → FreeAssocCat t t′

  module _ where
    open ≈-Reasoning

    nil : ∀ {t} → FreeAssocCat t t
    nil = MkFreeAssocCat []
    
    postulate TODO : {X : Set} → X
    
    cons : ∀ {t t′ t′′}
         → C t t′
         → FreeAssocCat t′ t′′
         → FreeAssocCat t t′′
    cons = TODO  -- a generalization of (exp→free (embed f)) ?

    ty-is-cons : ∀ t
               → Σ[ a ∈ A ]
                 Σ[ as ∈ List A ]
                 ty→list t ≡ a ∷ as
    ty-is-cons (atom a) = a , [] , refl
    ty-is-cons (t₁ , t₂) = let a , as , prf = ty-is-cons t₁
                            in a , as ++ ty→list t₂ , go a as prf
      where
        go : (a : A)
           → (as : List A)
           → (prf : ty→list t₁ ≡ a ∷ as)
           → ty→list (t₁ , t₂) ≡ a ∷ (as ++ ty→list t₂)
        go = TODO  -- doesn't look too hard...
    
    cons-is-solid : ∀ {a as} → SomeSolid (all Solid (a ∷ as))
    cons-is-solid = here
    
    type-is-solid : ∀ t → SomeSolid (all Solid (ty→list t))
    type-is-solid = TODO  -- use ty-is-cons to reduce the problem to cons-is-solid

    exp→free : ∀ {t t′} → Exp t t′ → FreeAssocCat t t′
    exp→free {t} {t′} (embed f) = MkFreeAssocCat (row′ ∷ [])
      where
        as₀ : List A
        as₀ = ty→list t

        as₀′ : List A
        as₀′ = ty→list t′

        ss₀ : SolidityList as₀
        ss₀ = all Solid as₀

        ss₀′ : SolidityList as₀′
        ss₀′ = all Solid as₀′

        row : Row {as₀ ++ []} {as₀′ ++ []} (ss₀ ++′ []) (ss₀′ ++′ [])
        row = piece f (type-is-solid t) []
        
        row′ : Row {as₀} {as₀′} ss₀ ss₀′
        row′ = TODO  -- prove that (++ []) is identity everywhere
    exp→free id           = nil
    exp→free (f <> g)     = TODO  -- make blocks from g fall down on f
    exp→free (_ ∥ _)      = TODO  -- concatenate rows pair-wise
    exp→free associate    = TODO  -- an empty pile?
    exp→free disassociate = TODO  -- an empty pile?
    
    free→exp : ∀ {a a′} → FreeAssocCat a a′ → Exp a a′
    free→exp = TODO

  module Sound where
    open ≈-Reasoning

    sound : ∀ {a a′} {e e′ : Exp a a′}
          → exp→free e ≡ exp→free e′
          → e ≈ e′
    sound = TODO

  module Complete where
    open ≡-Reasoning

    complete : ∀ {a a′} {e₁ e₂ : Exp a a′}
             → e₁ ≈ e₂ → exp→free e₁ ≡ exp→free e₂
    complete = TODO
