open import Function

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Data.String
open import Data.Nat as ℕ
open import Data.Nat.Properties

open import Data.List as List
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All as All

open import Data.List.Relation.Binary.Prefix.Heterogeneous
open import Data.List.Relation.Binary.Pointwise as PW
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality

module STLC (Name Ty : Set)
            (_?=_ : (x₁ x₂ : Name) → Dec (x₁ ≡ x₂)) where

-- This file contains a formalization of STLC with a notion of paths that should
-- suffice to implement the refactorings sketched at the end of this file.
--
-- The notion of paths is limited to dealing with lexical scoping.
--
-- To scale to non-lexical scoping, we need typing judgments to also yield
-- information about which scopes were constructed.
--
-- While we do not strictly need this information for lexical scoping, we will
-- need it for non-lexical scoping.
--
-- Furthermore, we desire a uniform data structure for name resolution.


-- Contexts
------------------------------------------------------------------------

Ctx = List (∃ λ (γ : List (Name × Ty)) → Unique (List.map proj₁ γ))


-- Indices
------------------------------------------------------------------------

data Index : (Γ : Ctx) (x : Name) (t : Ty) → Set where
  here  : ∀ {x t Γ} γ {u}
        → (x , t) ∈ γ
        → Index ((γ , u) ∷ Γ) x t
  there : ∀ {x t Γ} γ {u}
        → (x , t) ∉ γ
        → Index Γ x t
        → Index ((γ , u) ∷ Γ) x t


-- Path
------------------------------------------------------------------------

-- A path tells us the inner context that a path occurred in.

Path : Ctx → Name → Ty → Set
Path Γ x t = Maybe (Index Γ x t) × Ctx

here-dec : ∀ {γ u Γ x t} → (i : Index ((γ , u) ∷ Γ) x t) → Dec (∃ λ w → i ≡ here γ w)
here-dec (here  _ w) = yes (w , _≡_.refl)
here-dec (there _ x p) = no λ ()

peel : ∀ {γu Γ} → List (∃₂ (Path (γu ∷ Γ))) → List (∃₂ (Path Γ))
peel [] = []
peel {γu} ((x , t , just (here γ x₁) , c) ∷ xs) = (x , t , nothing , γu ∷ c) ∷ peel xs
peel {γu} ((x , t , just (there γ x₁ i) , c) ∷ xs) = (x , t , just i , γu ∷ c) ∷ peel xs
peel {γu} ((x , t , nothing , c) ∷ xs) = (x , t , nothing , γu ∷ c) ∷ peel xs


-- E.g., ∃ Γ′ . Path Γ x y × 


-- Resolution computations
------------------------------------------------------------------------

data Res (Γ : Ctx) (A : Set) : Set₁ where
  pure : A → Res Γ A
  look : (x : Name) → (Maybe (∃ λ t → Index Γ x t) → Res Γ A) → Res Γ A
  bind : {B : Set} (γ : List (Name × Ty)) (u : Unique (List.map proj₁ γ))
       → Res ((γ , u) ∷ Γ) B
       → (B → Res Γ A)
       → Res Γ A
  err  : String → Res Γ A


-- Monadic bind

_𝓑_ : ∀ {Γ A B} → Res Γ A → (A → Res Γ B) → Res Γ B
pure x 𝓑 k = k x
look x g 𝓑 k = look x (λ p → g p 𝓑 k)
bind γ u m g 𝓑 k = bind γ u m (λ x → g x 𝓑 k)
err s 𝓑 _ = err s


-- Running resolution computations
------------------------------------------------------------------------

conv₁ : ∀ {x t} {γ : List (Name × Ty)} → (x , t) ∈ γ → Any (λ y → x ≡ proj₁ y) γ
conv₁ (here _≡_.refl) = here _≡_.refl
conv₁ (there γ) = there (conv₁ γ)

conv₂ : ∀ {x} {γ : List (Name × Ty)} → Any (λ y → x ≡ proj₁ y) γ → ∃ λ t → (x , t) ∈ γ
conv₂ (here _≡_.refl) = _ , here _≡_.refl
conv₂ (there γ) = let (t , w) = conv₂ γ in t , there w

resolve : (Γ : Ctx) (x : Name) → Dec (∃ λ t → Index Γ x t)
resolve [] x = no (λ ())
resolve ((γ , u) ∷ Γ) x with any? (λ (x′ , _) → x ?= x′) γ | resolve Γ x
... | no ¬a | no ¬a₁ = no (λ where
  (t , here .γ x) → contradiction (conv₁ x) ¬a
  (t , there .γ x p) → contradiction (t , p) ¬a₁)
... | no ¬a | yes (t , p) = yes (t , there γ (¬a ∘ conv₁) p)
... | yes a | _ =
  yes (_ , here γ (proj₂ (conv₂ a)))

runRes : ∀ Γ {A} → Res Γ A → String ⊎ A
runRes Γ (pure x) = inj₂ x
runRes Γ (look x k) with resolve Γ x
... | yes x = runRes Γ (k (just x))
... | no ¬q = runRes Γ (k nothing)
runRes Γ (bind γ u m k) with runRes ((γ , u) ∷ Γ) m
... | inj₁ s = inj₁ s
... | inj₂ x = runRes Γ (k x)
runRes Γ (err x) = inj₁ x


-- Syntax of STLC
------------------------------------------------------------------------

module CaseSTLC (_↣_ : List Ty → Ty → Ty)
                (_≟_ : (t₁ t₂ : Ty) → Dec (t₁ ≡ t₂))
                (is↣ : (t : Ty) → Dec (∃₂ λ ts t′ → ts ↣ t′ ≡ t))
                (𝕟 : Ty) where

  variable Γ Γ₁ Γ₂ Γ′ Γ₁′ Γ₂′ : Ctx
           t t₁ t₂ t′ t₁′ t₂′ : Ty
           ts ts₁ ts₂ ts′ ts₁′ ts₂′ : List Ty

  data RSTLC : Set where
    rvar : (x : Name) → RSTLC
    rlam : (γ : List (Name × Ty)) → RSTLC → RSTLC
    rapp : RSTLC → List RSTLC → RSTLC
    rnum : ℕ → RSTLC

  data STLC : (Γ : Ctx) → List (∃₂ (Path Γ)) → Ty → Set where
    var : (x : Name) → (p : Index Γ x t) → STLC Γ ((x , t , just p , []) ∷ []) t
    lam : ∀ γ u {ps₁ ps}
        → STLC ((γ , u) ∷ Γ) ps₁ t′
        → List.map proj₂ γ ≡ ts
        → ps ≡ peel ps₁
        → STLC Γ ps (ts ↣ t′)
    app : ∀ {ps₁ pss₂ ps}
        → STLC Γ ps₁ (ts ↣ t₂)
        → Pointwise (STLC Γ) pss₂ ts
        → ps ≡ ps₁ List.++ List.concat pss₂
        → STLC Γ ps t₂
    num : ℕ → STLC Γ [] 𝕟


  -- STLC Erasure
  
  erases : ∀ {pss} → Pointwise (STLC Γ) pss ts → List (RSTLC)

  erase : ∀ {ps} → STLC Γ ps t → RSTLC
  erase (var x x₁) = rvar x
  erase (lam γ u e _ _) = rlam γ (erase e)
  erase (app e₁ es _) = rapp (erase e₁) (erases es)
  erase (num x) = rnum x

  erases [] = []
  erases (px ∷ x) = erase px ∷ erases x


  -- Type checker for STLC
  ------------------------------------------------------------------------

  -- Soundness

  Sound : Ctx → RSTLC → Set
  Sound Γ e = ∃ λ ps → ∃₂ λ (t : Ty) (e′ : STLC Γ ps t) → erase e′ ≡ e

  uniq-dec : (xs : List Name) → Dec (Unique xs)
  uniq-dec = allPairs? λ x y → ¬? (x ?= y)

  mutual
    tc : (r : RSTLC) → Res Γ (Sound Γ r)
    tc (rvar x) = look x (maybe (λ (t , i) → pure (_ , t , var x i , _≡_.refl)) (err "unbound variable"))
    tc (rlam γ b) with uniq-dec (List.map proj₁ γ)
    ... | no _ = err "λ binds same variable twice"
    ... | yes u = bind γ u (tc b) (λ (ps , t , b′ , eq) →
      pure (peel ps , List.map proj₂ γ ↣ t , lam γ u b′ _≡_.refl _≡_.refl , cong (rlam _) eq))
    tc (rapp e₁ es) = tc e₁ 𝓑 λ (ps , t₁ , e₁′ , eq) → case is↣ t₁ of λ where
      (no ¬a) → err "cannot apply non-function"
      (yes (ts , t₁′ , refl)) → case List.length es ℕ.≟ List.length ts of λ where
        (no _) → err "argument/parameter length mismatch"
        (yes eq₀) → tcs es ts eq₀ 𝓑 (λ (pss′ , es′ , eq′) →
          pure (_ , t₁′ , app e₁′ es′ _≡_.refl , cong₂ rapp eq eq′))
    tc (rnum n) = pure ([] , 𝕟 , num n , _≡_.refl)

    tcs : (es : List RSTLC) (ts : List Ty) → List.length es ≡ List.length ts
        → Res Γ (∃₂ λ (pss : List (List (∃₂ (Path Γ)))) (xs : Pointwise (STLC Γ) pss ts) → erases xs ≡ es)
    tcs [] [] eq = pure ([] , [] , _≡_.refl)
    tcs (e ∷ es) (t ∷ ts) eq = tc e 𝓑 λ (ps′ , t′ , e′ , eq′) → case t ≟ t′ of λ where
      (no _) → err "argument type mismatch"
      (yes refl) → tcs es ts (suc-injective eq) 𝓑 λ (pss′ , es′ , eq₁′) →
        pure (ps′ ∷ pss′ , e′ ∷ es′ , cong₂ _∷_ eq′ eq₁′)


--   -- Refactorings
--   ------------------------------------------------------------------------

--   -- Introduce binder (weakening 1)
--   --   if z is neither in [x,y], nor in paths of b,
--   --   λ x y . b --> λ z x y . intro b

--   -- Merge bindings (weakening 2)
--   --   if Unique [x,y,z],
--   --   λ x y . λ z . b --> λ x y z . merge b

--   -- Split binders into bindings (weakening 3)
--   --   λ x y . b --> λ x . λ y . split b

--   -- Reorder binders (weakening 4)
--   --   λ x y . b --> λ y x . reord b

--   -- Contract bindings
--   --   If y does not occur in an x-shadowing context
--   --   λ (x : T) (y : T) . b --> λ (x : T) . b[y/x]


--   -- Exchange bindings (corollary of merging, reordering, and splitting)
--   --   If Unique [x,y,r,q]
--   --   λ x y . λ r q . b --> λ r q . λ x y . exch b

--   -- Renaming (corollary of intro and contract)
--   --   If Unique [y,z] and x does not occur in a z-shadowing context
--   --   λ x y . b --> λ z y . b
