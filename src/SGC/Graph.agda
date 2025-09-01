open import Data.Nat as N
open import Data.Nat.Properties as NP
open import Data.Fin as F
open import Data.Fin.Properties as FP
open import Data.List as L
open import Data.List.Properties as LP
open import Data.List.Relation.Unary.All as A
open import Data.List.Relation.Binary.Pointwise
open import Data.List.Relation.Binary.Pointwise.Properties as PP
open import Data.List.Relation.Binary.Suffix.Heterogeneous
open import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties as HP
open import Data.Product

open import Relation.Binary.PropositionalEquality as E

module SGC.Graph (Name Lbl Ty RE : Set) (lex : Lbl) where

open import SGC.Core Name Lbl Ty RE

-- helper lemma

suffix-refl : {A : Set} {xs : List A} → Suffix _≡_ xs xs
suffix-refl = here (PP.refl E.refl)

record Edge (n : ℕ) : Set where
  constructor _-[_]->_
  field srcₑ : Fin n
        lblₑ : Lbl
        tgtₑ : Fin n
  

wk-edge : ∀ {n m} → n N.≤ m → Edge n → Edge m
wk-edge r (s -[ l ]-> t) = (inject≤ s r) -[ l ]-> (inject≤ t r)

wk-edges-refl : {n : ℕ} {es : List (Edge n)} → L.map (wk-edge NP.≤-refl) es
                                             ≡ es
wk-edges-refl = map-id-local (A.tabulate λ where
  {s -[ l ]-> t} _ → cong₂ (_-[ _ ]->_) (inject≤-refl _ NP.≤-refl) (inject≤-refl _ NP.≤-refl))

wk-edge-trans≡ : {n₁ n₂ n₃ : ℕ} (r₁ : n₁ N.≤ n₂) (r₂ : n₂ N.≤ n₃) (e : Edge n₁)
               → wk-edge r₂ (wk-edge r₁ e) ≡ wk-edge (NP.≤-trans r₁ r₂) e
wk-edge-trans≡ = {!!}

suffix-wk : ∀ {n m : ℕ} (es₁ es₂ : List (Edge n)) (r : n N.≤ m)
          → Suffix _≡_ es₁ es₂
          → Suffix _≡_ (L.map (wk-edge r) es₁) (L.map (wk-edge r) es₂)
suffix-wk = {!!}

record Graph : Set where
  constructor G⟨_∙_∙_⟩
  field sc#   : ℕ
        edges : List (Edge sc#)
        opn   : List (Fin sc#)

open Graph

record _⊑_ (g₁ g₂ : Graph) : Set where
  constructor ⊑⟨_∙_⟩
  field sc#⊑   : sc# g₁ N.≤ sc# g₂
        edges⊑ : Suffix _≡_ (L.map (wk-edge sc#⊑) (edges g₁)) (edges g₂)

open _⊑_

⊑-refl : ∀ {g} → g ⊑ g
sc#⊑ ⊑-refl = NP.≤-refl
edges⊑ ⊑-refl = subst (λ X → Suffix _≡_ X _) (sym wk-edges-refl) suffix-refl

⊑-trans : ∀ {g₁ g₂ g₃} → g₁ ⊑ g₂ → g₂ ⊑ g₃ → g₁ ⊑ g₃
sc#⊑ (⊑-trans r₁ r₂) = NP.≤-trans (sc#⊑ r₁) (sc#⊑ r₂)
edges⊑ (⊑-trans {g₁} {g₂} r₁ r₂) = HP.trans E.trans
  (let x = suffix-wk _ _ (sc#⊑ r₂) (edges⊑ r₁) in
    subst (λ X → Suffix _≡_ X _)
          (E.trans
            (sym (map-∘ (edges g₁)))
            (map-cong (λ x → wk-edge-trans≡ (sc#⊑ r₁) (sc#⊑ r₂) x) (edges g₁)))
          x)
  (edges⊑ r₂)

resolve : RE → ? → ?

runM : ∀ (g₁ : Graph) {P} → M (sc# g₁) (opn g₁) P → ∃ λ g₂ → g₁ ⊑ g₂ × P (sc# g₂)
runM g (pure x) = g , ⊑-refl , x
runM g (imp φ φ′ l x₁ x₂ m) = let
    g′ = G⟨ (sc# g) ∙ ((φ -[ l ]-> φ′) ∷ edges g) ∙ opn g ⟩
    (g″ , ext , p)  = runM g′ m
  in g″
   , ⊑-trans
       ⊑⟨ NP.≤-refl ∙ (there (subst (λ X → Suffix _≡_ X _) (sym wk-edges-refl) suffix-refl)) ⟩
       ext
   , p
runM g (new φ m k) = let
    g′ = G⟨ N.suc (sc# g)
          ∙ L.map (wk-edge (n≤1+n _)) (edges g)
          ∙ fromℕ (sc# g) ∷ L.map (λ x → inject≤ x (n≤1+n _)) (opn g) ⟩
    (g″ , ext , _) = runM g′ m
    g₁ = G⟨ N.suc (sc# g)
          ∙ ((fromℕ (sc# g)) -[ lex ]-> inject≤ φ (n≤1+n _)) ∷ L.map (wk-edge (n≤1+n _)) (edges g)
          ∙ L.map (λ x → inject≤ x (n≤1+n _)) (opn g) ⟩
    (g₂ , ext′ , p) = runM g₁ (k (n≤1+n _))
  in g₂ , (⊑-trans ⊑⟨ (n≤1+n _)
                    ∙ there (here (PP.refl E.refl)) ⟩
                   ext′) , p
runM g (res re o m) = {!!}

