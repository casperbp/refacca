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
    (tl tu : Ty)
    (∶≤ : ∀ {l x} → DecPoset._≤_ LDP (x ∶ tl) l → DecPoset._≤_ LDP l (x ∶ tu) → ∃ λ t → l ≡ x ∶ t)
    (lex : Lbl)
  where

open DecPoset LDP renaming (_≤?_ to _L≤?_; _≈_ to _L≈_)

private
  po = DecPoset.preorder LDP

open import Text.Regex.Base po as R
open import Text.Regex.Derivative.Brzozowski LDP as RB
open import Text.Regex.Properties LDP as RP
open import SGC.Core Name Ty LDP

-- helper lemmas

suffix-refl : {A : Set} {xs : List A} → Suffix _≡_ xs xs
suffix-refl = here (PP.refl E.refl)

pw-refl : {A : Set} {xs ys : List A} → Pointwise _≡_ xs ys → xs ≡ ys
pw-refl [] = E.refl
pw-refl (x∼y ∷ x) = cong₂ _∷_ x∼y (pw-refl x)


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
wk-edge-trans≡ r₁ r₂ e = cong₂ _-[ _ ]->_ (inject≤-trans _ r₁ r₂) (inject≤-trans _ r₁ r₂)

suffix-wk : ∀ {n m : ℕ} (es₁ es₂ : List (Edge n)) (r : n N.≤ m)
          → Suffix _≡_ es₁ es₂
          → Suffix _≡_ (L.map (wk-edge r) es₁) (L.map (wk-edge r) es₂)
suffix-wk es₁ es₂ r (here x) with pw-refl x
... | E.refl = here (PP.refl E.refl)
suffix-wk es₁ .(_ ∷ _) r (there x) = there (suffix-wk es₁ _ r x)

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
        → (re : Exp)            -- regex
        → (φ : Fin (sc# g))     -- cur scope
        → Err ⊎ (∃ λ w → Path g φ w × w R.∈ re)  -- res

res1 : (g : Graph)
     → List (Fin (sc# g))    -- seens
     → (re : Exp)            -- regex
     → (φ : Fin (sc# g))
     → List (∃ λ (e : Edge (sc# g)) → srcₑ e ≡ φ × e LM.∈ edges g)   -- edges to try
     → Err ⊎ (∃ λ w → Path g φ w × w R.∈ re)

res2 : (g : Graph)
     → List (Fin (sc# g))    -- seens
     → (re : Exp)            -- regex
     → (φ : Fin (sc# g))
     → List (∃ λ (e : Edge (sc# g)) → srcₑ e ≡ φ × e LM.∈ edges g) -- edges to try
     → Err ⊎ (∃ λ w → Path g φ w × w R.∈ re)

res1 g φs r φ = foldr
  (λ (e , eq , lw) m →
    ( (λ e → e 𝓣 m)
    ∇ (λ (w , p , q) →
         ( (λ _ → inj₂ (lblₑ e ∷ w , step e eq lw p E.refl , eat-sound (lblₑ e) r q))
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


-- Fixme: missing check for when r is empty.
resolve g φs r φ with A?.any? (φ FP.≟_) φs
... | yes _ = inj₁ resolution-error -- cycle detected
... | no  _ = let
    es = outgoing φ r (edges g)
  in res2 g φs r φ es

runM : ∀ (g₁ : Graph) {P} → M (sc# g₁) (opn g₁) P → Err ⊎ (∃ λ g₂ → g₁ ⊑ g₂ × P (sc# g₂))
runM g (pure x) = inj₂ (g , ⊑-refl , x)
runM g (imp φ φ′ l x₁ x₂ m) = let
    g′ = G⟨ (sc# g) ∙ ((φ -[ l ]-> φ′) ∷ edges g) ∙ opn g ⟩
    r = runM g′ m
  in ( inj₁
     ∇ λ (g″ , ext , p) → inj₂
              ( g″
              , ⊑-trans
                  ⊑⟨ NP.≤-refl ∙ (there (subst (λ X → Suffix _≡_ X _) (sym wk-edges-refl) suffix-refl)) ⟩
                  ext
              , p ) )
     r
runM g (new φ m k) = let
    g′ = G⟨ N.suc (sc# g)
          ∙ L.map (wk-edge (n≤1+n _)) (edges g)
          ∙ fromℕ (sc# g) ∷ L.map (λ x → inject≤ x (n≤1+n _)) (opn g) ⟩
    r₁ = runM g′ m
  in ( inj₁
     ∇ λ (g″ , ext , _) → let
         g₁ = G⟨ sc# g″
               ∙ (inject≤ (fromℕ (sc# g)) (sc#⊑ ext)
                   -[ lex ]->
                     inject≤ φ (NP.≤-trans (n≤1+n _) (sc#⊑ ext)))
                 ∷ edges g″
               ∙ L.map (λ x → inject≤ x (NP.≤-trans (n≤1+n _) (sc#⊑ ext))) (opn g) ⟩
         r₂ = runM g₁ (k (NP.≤-trans (n≤1+n _) (sc#⊑ ext)))
       in ( inj₁
          ∇ λ (g₂ , ext′ , p) →
            inj₂ ( g₂
                 , ⊑-trans ⊑⟨ NP.≤-trans (n≤1+n _) (sc#⊑ ext)
                              ∙ there (HP.trans E.trans
                                         (subst (Suffix _≡_ (L.map
                                                               (wk-edge
                                                                (NP.≤-trans (n≤1+n (sc# g))
                                                                 (sc#⊑ ext)))
                                                               (edges g)))
                                                (E.trans
                                                  (sym
                                                    (map-cong
                                                      (wk-edge-trans≡ (n≤1+n _) (sc#⊑ ext))
                                                      (edges g)))
                                                  (map-∘ _))
                                                suffix-refl)
                                         (edges⊑ ext)) ⟩ ext′
                 , p ) )
          r₂ )
     r₁
runM g (res re x φ m) = let r = resolve g [] (re R.∙ R.[ (x ∶ tl) R.─ (x ∶ tu) ∷ [] ]) φ
  in ( inj₁
     ∇ λ (w , _ , q) → runM g (m (extr re x q)) )
     r
  where
    extr : ∀ {w : List Lbl} (re : Exp) (x : Name)
         → w R.∈ (re R.∙ (R.[ (x ∶ tl) R.─ (x ∶ tu) ∷ [] ]))
         → Ty
    extr re x (prod eq r₁ [ here (x₁ R.─ x₂) ]) = let (t , _) = ∶≤ x₁ x₂ in t


