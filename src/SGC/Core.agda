module SGC.Core (Name Lbl Ty RE : Set) where

open import Function

open import Data.Empty
open import Data.Unit
open import Data.Nat as N
open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat.Properties as NP
open import Data.List as L
open import Data.List.Properties
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All as A

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data M (n : ℕ)
       (Open : List (Fin n))
       (P : ℕ → Set) : Set₁ where
  pure : P n → M n Open P
  imp  : (φ φ′ : Fin n)
       → Lbl
       → φ ∈ Open
       → φ′ ∉ Open
       → M n Open P
       → M n Open P
  new  : (φ : Fin n)
       → let m = suc n
             φ′ = fromℕ n in
         M m (φ′ ∷ L.map (λ x → inject≤ x (n≤1+n _)) Open) (λ _ → ⊤)
       → (∀ {m} (r : n N.≤ m) → M m (L.map (λ x → inject≤ x r) Open) P)
       → M n Open P
  res  : RE
       → (_≤L_ : (l₁ l₂ : Lbl) → Set)
       → (dec : (l₁ l₂ : Lbl) → Dec (l₁ ≤L l₂))
       → (Ty → M n Open P) → M n Open P

postulate renameM : ∀ {n Open P} (f : Fin n → Fin (suc n)) → M n Open P → M (suc n) (L.map f Open) (P ∘ suc)

All-inject-refl≤ : ∀ {n} (Open : List (Fin n)) → All (λ x → inject≤ x (NP.≤-reflexive refl) ≡ x) Open
All-inject-refl≤ [] = []
All-inject-refl≤ (x ∷ o) = inject≤-refl x (NP.≤-reflexive refl) ∷ All-inject-refl≤ o

inj-le : ∀ {n m} (r : n N.≤ m) (φ : Fin n) → suc (inject≤ φ r) ≡ inject≤ (suc φ) (s≤s r)
inj-le (s≤s r) zero = refl
inj-le r (suc φ) = refl

_⊢_𝓑_ : ∀ {n Open P Q}
      → (∀ n m → n N.≤ m → P n → P m)
      → M n Open P → (∀ m → (r : n N.≤ m) → P m → M m (L.map (λ x → inject≤ x r) Open) Q) → M n Open Q
_ ⊢ pure x 𝓑 k = subst (λ Open → M _ Open _) (map-id-local (All-inject-refl≤ _)) (k _ (NP.≤-reflexive refl) x)
w ⊢ imp n n′ l x₁ x₂ m 𝓑 k = imp n n′ l x₁ x₂ (w ⊢ m 𝓑 k)
_⊢_𝓑_ {Open = Open} w (new φ m m₁) k = new φ m λ x → w ⊢ m₁ x 𝓑 λ m₂ r x₁ →
  subst (λ Open → M _ Open _)
        (trans (sym (map-cong-local (A.tabulate (λ _ → inject≤-trans _ x r)))) (map-∘ Open))
        (k m₂ (NP.≤-trans x r) x₁)
w ⊢ res o d r m 𝓑 k = res o d r (λ x → w ⊢ m x 𝓑 k)


