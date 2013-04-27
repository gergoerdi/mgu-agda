module S where

-- https://github.com/wjzz/agda-DTP-examples/blob/master/Unification/Unification.agda

open import Data.Nat
open import Data.Fin
-- open import Data.Fin.Props renaming (_≟_ to _F≟_)
open import Function using (_∘_; _⟨_⟩_)

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Empty

open import Data.Maybe
open import Category.Applicative
open import MaybeExtras
open import Level using () renaming (zero to ℓ₀)
open RawApplicative {ℓ₀} Data.Maybe.applicative

open import ThinThick

TV : ℕ → Set
TV = Fin

Con : Set
Con = ℕ

data Type (n : ℕ) : Set where
  -- TCon : Con → Type n
  TCon : Type n
  TVar : TV n → Type n
  TApp : Type n → Type n → Type n

rename : {n m : ℕ} → (Fin m → Fin n) → (Fin m → Type n)
rename f = TVar ∘ f

substitute : {n m : ℕ} → (Fin n → Type m) → (Type n → Type m)
substitute f (TVar i)    = f i
substitute f TCon        = TCon
substitute f (TApp t t′) = TApp (substitute f t) (substitute f t′)

bind : {n m l : ℕ} → (Fin m → Type n) → (Fin l → Type m) → (Fin l → Type n)
bind f g = substitute f ∘ g

occurs-check : ∀ {n} (x : Fin (suc n)) → Type (suc n) → Maybe (Type n)
occurs-check x TCon = just TCon
occurs-check x (TVar y) = TVar <$> thick x y
occurs-check x (TApp t₁ t₂) = TApp <$> occurs-check x t₁ ⊛ occurs-check x t₂

_for_ : {n : ℕ} → (t : Type n) → (x : Fin (suc n)) → Fin (suc n) → Type n
(t for x) y = maybe′ TVar t (thick x y)

module for-Props where
  for-thin : ∀ {n} {t : Type n} {x y} → (t for x) (thin x y) ≡ TVar y
  for-thin {n} {t} {x} {y} with thick x (thin x y) | inspect (thick x) (thin x y)
  for-thin {n} {t} {x} {y} | just y′ | [ eq ] = cong TVar (thin-inj x (sym (Partial-Just (subst (Partial _ _) eq (thick-thin x (thin x y))))))
  for-thin {n} {t} {x} {y} | nothing | [ eq ] = ⊥-elim (thin-nofix x (Partial-Nothing (subst (Partial _ _) eq (thick-thin x (thin x y)))))

  for-unify : ∀ {n} x (t : Type (suc n)) {t′ : Type n} → occurs-check x t ≡ just t′ →
              substitute (t′ for x) t ≡ (t′ for x) x
  for-unify x t eq = {!!}
