open import Level renaming (suc to ℓsuc; zero to ℓ0)

open import Data.Nat as N
open import Data.Nat.Properties as NP

open import Data.Bool
open import Data.Sum renaming ([_,_] to _∇_)

open import Data.Fin as F
open import Data.Fin.Properties as FP

open import Data.List as L
open import Data.List.Membership.Propositional as LM
open import Data.List.Properties as LP
open import Data.List.Relation.Unary.Any as A?
open import Data.List.Relation.Unary.All as A
open import Data.List.Relation.Binary.Pointwise
open import Data.List.Relation.Binary.Pointwise.Properties as PP
open import Data.List.Relation.Binary.Suffix.Heterogeneous
open import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties as HP

open import Data.Product

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.Bundles using (DecPoset)
open import Relation.Binary.PropositionalEquality as E
open import Relation.Binary.Definitions using (DecidableEquality)

module SGC.Graph
    (Name Ty : Set)
    (LDP : DecPoset ℓ0 ℓ0 ℓ0)
    (let Lbl = DecPoset.Carrier LDP)
    (_∶_ : Name → Ty → Lbl)
    (lex : Lbl)
  where

open DecPoset LDP renaming (_≤?_ to _L≤?_)
open import Text.Regex LDP as R
open import Text.Regex.Derivative.Brzozowski LDP as RB
open import Text.Regex.Properties LDP as RP
open import SGC.Core Name Ty LDP

-- helper lemmas

suffix-refl : {A : Set} {xs : List A} → Suffix _≡_ xs xs
suffix-refl = here (PP.refl E.refl)

-- Edges
------------------------------------------------------------------------

record Edge (n : ℕ) : Set where
  constructor _-[_]->_
  field srcₑ : Fin n
        lblₑ : Lbl
        tgtₑ : Fin n
  

open Edge

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


Word = List Lbl

data Path (g : Graph) : Fin (sc# g) → Word → Set where
  step : ∀ {s w w′} (e : Edge (sc# g))
       → srcₑ e ≡ s
       → e LM.∈ edges g
       → Path g (tgtₑ e) w
       → w′ ≡ lblₑ e ∷ w
       → Path g s w′
  stop : ∀ {s} → Path g s []


-- filter : ∀ {P : Pred A p} → Decidable P → List A → List A
-- filter P? [] = []
-- filter P? (x ∷ xs) =
--   let xs′ = filter P? xs in
--   if does (P? x)
--     then x ∷ xs′
--     else xs′

outgoing : ∀ {n} → (φ : Fin n)
         → Exp
         → (es : List (Edge n))
         → List (∃ λ (e : Edge n) → srcₑ e ≡ φ × e LM.∈ es)
outgoing φ r [] = []
outgoing φ r (e ∷ xs) with (srcₑ e FP.≟ φ) ×-dec (¬? (is-∅ (eat (lblₑ e) r)))
... | yes (eq , p) = let xs′ = outgoing φ r xs
  in (e , eq , here E.refl) ∷ L.map (λ (e′ , eq′ , w′) → e′ , eq′ , there w′) xs′
... | no ¬p = let xs′ = outgoing φ r xs
  in L.map (λ (e′ , eq′ , w′) → e′ , eq′ , there w′) xs′

least-elements : ∀ {n φ es} → List (∃ λ (e : Edge n) → srcₑ e ≡ φ × e LM.∈ es)
               → List (∃ λ (e : Edge n) → srcₑ e ≡ φ × e LM.∈ es)
               × List (∃ λ (e : Edge n) → srcₑ e ≡ φ × e LM.∈ es)
least-elements es =
  partition (λ (e₁ , eq) → A.all? (λ (e₂ , _) → -- y L≤? x →-dec 
    lblₑ e₁ L≤? lblₑ e₂) es) es

data Err : Set where
  resolution-error ambiguity-error : Err

_𝓣_ : ∀ {A : Set} → Err → (Err ⊎ A) → (Err ⊎ A)
ambiguity-error 𝓣 (inj₁ _) = inj₁ ambiguity-error
_ 𝓣 m = m

{-# TERMINATING #-}
resolve : (g : Graph)           -- cur graph
        → List (Fin (sc# g))    -- seens (cycle detection)
        → Exp                   -- regex
        → (φ : Fin (sc# g))     -- cur scope
        → Err ⊎ (∃ (Path g φ))  -- res

res1 : (g : Graph)
     → List (Fin (sc# g))    -- seens
     → Exp                   -- regex
     → (φ : Fin (sc# g))
     → List (∃ λ (e : Edge (sc# g)) → srcₑ e ≡ φ × e LM.∈ edges g)   -- edges to try
     → Err ⊎ (∃ (Path g φ))  -- 

res2 : (g : Graph)
     → List (Fin (sc# g))    -- seens
     → Exp                   -- regex
     → (φ : Fin (sc# g))
     → List (∃ λ (e : Edge (sc# g)) → srcₑ e ≡ φ × e LM.∈ edges g) -- edges to try
     → Err ⊎ (∃ (Path g φ))  -- 

res1 g φs r φ = foldr
  (λ (e , eq , lw) m →
    ( (λ e → e 𝓣 m)
    ∇ (λ (w , p) →
         ( (λ _ → inj₂ (lblₑ e ∷ w , step e eq lw p E.refl))
         ∇ λ _ → inj₁ ambiguity-error )
         m) )
    (resolve g (φ ∷ φs) (eat (lblₑ e) r) (tgtₑ e)))
  (inj₁ resolution-error)

res2 g φs r φ [] = inj₁ resolution-error
res2 g φs r φ es@(_ ∷ _) = let
    (least , rest) = least-elements es
  in ( (λ _ → res2 g φs r φ rest)
     ∇ inj₂ )
     (res1 g φs r φ least)


resolve g φs r φ with A?.any? (φ FP.≟_) φs
... | yes _ = inj₁ resolution-error -- cycle detected
... | no  _ = let
    es = outgoing φ r (edges g)
  in res2 g φs r φ es

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
runM g (res re m) = {!!}

