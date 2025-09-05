open import Function

open import Level renaming (suc to ℓsuc; zero to ℓ0)

open import Data.Empty
open import Data.Unit
open import Data.Product

open import Data.Nat as N
open import Data.Nat.Properties as NP

open import Data.Fin
open import Data.Fin.Properties

open import Data.List as L
open import Data.List.Properties
open import Data.List.Membership.Propositional as LM
open import Data.List.Relation.Unary.All as A

open import Relation.Unary
open import Relation.Binary.Bundles using (DecPoset)
open import Relation.Binary.PropositionalEquality

module SGF.Core
    (Name Ty : Set)
    (LDP : DecPoset ℓ0 ℓ0 ℓ0)
    (let Lbl = DecPoset.Carrier LDP)
  where

open import Text.Regex LDP as R

record Edge (n n′ : ℕ) : Set where
  constructor _-[_]->_
  field srcₑ : Fin n
        lblₑ : Lbl
        tgtₑ : Fin n′
open Edge

record Graph : Set where
  constructor G⟨_∙_⟩
  field sc#   : ℕ
        edges : List (Edge sc# sc#)
open Graph

record Extension (g : Graph) : Set where
  constructor E⟨_∙_⟩
  field ex#   : ℕ
        edges : List (Edge ex# (g .sc# N.+ ex#))
open Extension

postulate wk-Edge : ∀ {n n′ m m′} → n N.≤ n′ → m N.≤ m′ → Edge n m → Edge n′ m′

record World : Set where
  constructor W⟨_∙_⟩
  field wgr : Graph
        wex   : Extension wgr
open World

Word = List Lbl

data Path (w : World) : Fin (w .wgr .sc#) → Word → Set where
  step : ∀ {s ls ls′} (e : Edge (w .wgr .sc#) (w .wgr .sc#))
       → srcₑ e ≡ s
       → e LM.∈ (w .wgr .edges)
       → Path w (tgtₑ e) ls
       → ls′ ≡ lblₑ e ∷ ls
       → Path w s ls′
  stop : ∀ {s} → Path w s []

syntax Path w s ls = s via ls ! w

cmit : World → World
wgr (cmit w) = G⟨ (w .wgr .sc# N.+ w .wex .ex#) 
                  ∙ L.map (λ e →
                             (srcₑ e ↑ˡ w .wex .ex#)
                               -[ (lblₑ e) ]-> (tgtₑ e ↑ˡ w .wex .ex#))
                          (w .wgr .edges)
                    ++ L.map (λ e →
                               (w .wgr .sc# ↑ʳ srcₑ e)
                                 -[ lblₑ e ]-> tgtₑ e)
                             (w .wex .edges) ⟩
wex (cmit w) = E⟨ 0 ∙ [] ⟩

nw : World → World
wgr (nw w) = w .wgr
ex# (wex (nw w)) = suc (w . wex .ex#)
edges (wex (nw w)) = L.map
  (λ e → inject₁ (srcₑ e) -[ lblₑ e ]-> subst Fin (trans (cong (N._+ (w .wex .ex#)) (+-comm 1 (w .wgr .sc#))) ((+-assoc (w .wgr .sc#) 1 _))) (inject₁ (tgtₑ e)))
  (w .wex .edges)

WSet : (a : Level) → Set (ℓsuc a)
WSet a = World → Set a

Graph-sc#-inv : ∀ {g g′} → g ≡ g′ → g .sc# ≡ g′ .sc#
Graph-sc#-inv refl = refl

data _⊑_ (w w′ : World) : Set where
  ⊑-trans : ∀ {w₁}
          → w ⊑ w₁
          → w₁ ⊑ w′
          → w ⊑ w′
  ⊑◦      : (eq : w .wgr ≡ w′ .wgr)
          → (lt : w .wex .ex# N.≤ w′ .wex .ex#)
          → All (LM._∈ w′ .wex .edges)
                (L.map
                  (λ e → wk-Edge lt (+-monoʳ-≤ _ lt) (subst (λ X → Edge _ (X N.+ _)) (Graph-sc#-inv eq) e))
                  (w .wex .edges))
          → w ⊑ w′
  ⊑• : w′ ≡ cmit w
     → w ⊑ w′

variable a : Level

-- Open for extension; cannot be queried
Sc◦ : WSet ℓ0
Sc◦ w = Fin (w .wex .ex#)

-- Closed for extension; can be queried
Sc• : WSet ℓ0
Sc• w = Fin (w .wgr .sc#)

-- Can be either
Sc : WSet ℓ0
Sc w = Fin (w .wgr .sc# N.+ w .wex .ex#)


-- ⊑-refl : ∀ {g} → g ⊑ g
-- N⊑ ⊑-refl = NP.≤-refl
-- E⊑ ⊑-refl = A.tabulate
--   (λ x → subst
--     (_ LM.∈_)
--     (map-id-local
--       (A.tabulate
--         (λ x →
--           (cong₂ (_-[ _ ]->_)) (inject≤-refl _ _) (inject≤-refl _ _))))
--     x)

postulate
  ⊑-refl : ∀ {w} → w ⊑ w
  ⊑-cmit : ∀ {w w′} → cmit w ⊑ w′ → w ⊑ w′
  ⊑-nw   : ∀ {w w′} → nw w ⊑ w′ → w ⊑ w′
  
  Sc•-wk : ∀ {w w′} → w ⊑ w′ → Sc• w → Sc• w′

  -- Key lemma!  Follows from the fact that we only ever add
  -- ingoing edges, which cannot alter paths.
  Path-wk : ∀ {w w′ s ls} (ext : w ⊑ w′) (p : Path w s ls)
          → Path w′ (Sc•-wk ext s) ls




L : WSet ℓ0
L _ = Lbl

ℓ1 = ℓsuc ℓ0

data M (P : WSet ℓ1) : WSet ℓ1 where
  pure   : ∀[ P ⇒ M P ]
  edge   : ∀[ Sc◦ ⇒ L ⇒ Sc ⇒ M P ⇒ M P ]
  commit : ∀ {Q}
         → ∀[ Q ⇒ (Q ⇒ M P) ∘ cmit ⇒ M P ]
  query  : ∀ {w ls}
         → Exp
         → (s : Sc• w) → (Path w s ls → M P w) → M P w
  new    : ∀[ M P ∘ nw ⇒ M P ]

-- -- postulate renameM : ∀ {n Open P} (f : Fin n → Fin (suc n)) → M n Open P → M (suc n) (L.map f Open) (P ∘ suc)

-- -- All-inject-refl≤ : ∀ {n} (Open : List (Fin n)) → All (λ x → inject≤ x (NP.≤-reflexive refl) ≡ x) Open
-- -- All-inject-refl≤ [] = []
-- -- All-inject-refl≤ (x ∷ o) = inject≤-refl x (NP.≤-reflexive refl) ∷ All-inject-refl≤ o

-- -- inj-le : ∀ {n m} (r : n N.≤ m) (φ : Fin n) → suc (inject≤ φ r) ≡ inject≤ (suc φ) (s≤s r)
-- -- inj-le (s≤s r) zero = refl
-- -- inj-le r (suc φ) = refl

_⇛_ : WSet a → WSet a → WSet a
(P ⇛ Q) w = ∀[ w ⊑_ ⇒ (P ⇒ Q) ]

extend : ∀ {P Q} → ∀[ (Q ⇛ M P) ⇒ M Q ⇒ M P ]
extend k (pure x) = k ⊑-refl x
extend k (edge s l s′ g) = edge s l s′ (extend k g)
extend k (commit {Q = Q} q g) = commit {Q = Q} q (extend (λ ext → k (⊑-cmit ext)) ∘ g)
extend k (query re s g) = query re s (extend k ∘ g)
extend k (new g) = new (extend (λ ext → k (⊑-nw ext)) g)

