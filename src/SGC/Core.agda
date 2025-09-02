open import Function

open import Level renaming (suc to ℓsuc; zero to ℓ0)

open import Data.Empty
open import Data.Unit

open import Data.Nat as N
open import Data.Nat.Properties as NP

open import Data.Fin
open import Data.Fin.Properties

open import Data.List as L
open import Data.List.Properties
open import Data.List.Membership.Propositional as LM
open import Data.List.Relation.Unary.All as A

open import Relation.Binary.Bundles using (DecPoset)
open import Relation.Binary.PropositionalEquality

module SGC.Core
    (Name Ty : Set)
    (LDP : DecPoset ℓ0 ℓ0 ℓ0)
    (let Lbl = DecPoset.Carrier LDP)
  where

open import Text.Regex LDP as R

data M (n : ℕ)
       (Open : List (Fin n))
       (P : ℕ → Set) : Set₁ where
  pure : P n → M n Open P
  imp  : (φ φ′ : Fin n)
       → Lbl
       → φ LM.∈ Open
       → φ′ LM.∉ Open
       → M n Open P
       → M n Open P
  new  : (φ : Fin n)
       → let m = suc n
             φ′ = fromℕ n in
         M m (φ′ ∷ L.map (λ x → inject≤ x (n≤1+n _)) Open) (λ _ → ⊤)
       → (∀ {m} (r : n N.≤ m) → M m (L.map (λ x → inject≤ x r) Open) P)
       → M n Open P
  res  : Exp
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
w ⊢ res r m 𝓑 k = res r (λ x → w ⊢ m x 𝓑 k)


