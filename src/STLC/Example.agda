module STLC.Example where

open import Data.String
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Unique.Propositional.Properties
open import Data.List.Relation.Binary.Pointwise as PW

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data Ty : Set where
  𝕟 : Ty
  _↣_ : List Ty → Ty → Ty

_=?s_ : (xs ys : List Ty) → Dec (xs ≡ ys)

_=?_ : (t₁ t₂ : Ty) → Dec (t₁ ≡ t₂)
𝕟 =? 𝕟 = yes _≡_.refl
𝕟 =? (x ↣ t₂) = no λ ()
(x ↣ t₁) =? 𝕟 = no λ ()
(x ↣ t₁) =? (x₁ ↣ t₂) with x =?s x₁ | t₁ =? t₂
... | yes refl | yes refl = yes _≡_.refl
... | no ¬p | _ = no λ where refl → contradiction _≡_.refl ¬p
... | _ | no ¬p = no λ where refl → contradiction _≡_.refl ¬p

[] =?s [] = yes _≡_.refl
[] =?s (x ∷ ys) = no λ ()
(x ∷ xs) =?s [] = no λ ()
(x ∷ xs) =?s (x₁ ∷ ys) with x =? x₁ | xs =?s ys
... | yes refl | yes refl = yes _≡_.refl
... | no ¬p | _ = no λ where refl → contradiction _≡_.refl ¬p
... | _ | no ¬p = no λ where refl → contradiction _≡_.refl ¬p

is↣ : (t : Ty) → Dec (∃₂ λ ts t′ → ts ↣ t′ ≡ t)
is↣ 𝕟 = no λ ()
is↣ (x ↣ t) = yes (x , t , _≡_.refl)

open import STLC String Ty _≟_
open CaseSTLC _↣_ _=?_ is↣ 𝕟

-- Examples
------------------------------------------------------------------------

test-tc₀ : runRes [] (tc (rapp (rlam ( ("x" , 𝕟)
                                     ∷ ("y" , ((𝕟 ∷ []) ↣ 𝕟))
                                     ∷ [])
                                 (rvar "y"))
                               ( rnum 42
                               ∷ rlam (("z" , 𝕟) ∷ []) (rvar "z")
                               ∷ [])))
         ≡ inj₂ ( ( ( "y"
                    , (𝕟 ∷ []) ↣ 𝕟
                    , nothing
                    , ( ( ("x" , 𝕟) ∷ ("y" , (𝕟 ∷ []) ↣ 𝕟) ∷ []
                        , ((λ ()) ∷ []) ∷ [] ∷ [] )
                      ∷ [] ))
                  ∷ ( "z"
                    , 𝕟
                    , nothing
                    , ( ( ("z" , 𝕟) ∷ []
                        , [] ∷ [] )
                      ∷ [] ) )
                  ∷ [] )
                , (𝕟 ∷ []) ↣ 𝕟
                , app (lam (("x" , 𝕟) ∷ ("y" , ((𝕟 ∷ []) ↣ 𝕟)) ∷ [])
                           (((λ ()) ∷ []) ∷ [] ∷ [])
                           (var "y" (here _ (there (here _≡_.refl))))
                           _≡_.refl
                           _≡_.refl)
                      ( num 42
                      ∷ lam (("z" , 𝕟) ∷ []) ([] ∷ []) (var "z" (here _ (here _≡_.refl))) _≡_.refl _≡_.refl
                      ∷ [])
                      _≡_.refl
                , _≡_.refl )
test-tc₀ = _≡_.refl


test-shadow-tc :
    runRes [] (tc (rlam (("x" , 𝕟) ∷ ("y" , 𝕟) ∷ []) (rlam (("x" , 𝕟) ∷ []) (rvar "x"))))
  ≡ inj₂ ( ( ("x" , 𝕟 , nothing , (((("x" , 𝕟) ∷ ("y" , 𝕟) ∷ []) , _) ∷ (("x" , 𝕟) ∷ [] , _) ∷ []))
           ∷ [] )
         , ((𝕟 ∷ 𝕟 ∷ []) ↣ ((𝕟 ∷ []) ↣ 𝕟) )
         , lam (("x" , 𝕟) ∷ ("y" , 𝕟) ∷ [])
               (((λ ()) ∷ []) ∷ [] ∷ [])
               (lam (("x" , 𝕟) ∷ [])
                    ([] ∷ [])
                    (var "x" (here _ (here _≡_.refl)))
                    _≡_.refl
                    _≡_.refl)
               _≡_.refl
               _≡_.refl
         , _≡_.refl)
test-shadow-tc = _≡_.refl
