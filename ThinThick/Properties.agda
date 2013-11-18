module ThinThick.Properties where

open import ThinThick

open import Data.Nat
open import Data.Fin
open import Function using (_∘_; _⟨_⟩_)

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty

private
  -- Not exproted from Data.Fin.Props :(
  drop-suc : ∀ {o} {m n : Fin o} → Fin.suc m ≡ suc n → m ≡ n
  drop-suc refl = refl

thin-inj : ∀ {n} x {y z} → thin {n} x y ≡ thin x z → y ≡ z
thin-inj {zero} _ {()} eq
thin-inj {suc n} zero refl = refl
thin-inj {suc n} (suc x) {zero} {zero} refl = refl
thin-inj {suc n} (suc x) {zero} {suc z} ()
thin-inj {suc n} (suc x) {suc y} {zero} ()
thin-inj {suc n} (suc x) {suc y} {suc z} eq = cong suc (thin-inj x (drop-suc eq))

thin-nofix : ∀ {n} x {y} → thin {n} x y ≢ x
thin-nofix zero ()
thin-nofix (suc x) {zero} ()
thin-nofix (suc x) {suc y} eq = thin-nofix x (drop-suc eq)

thin-solve : ∀ {n} x y → x ≢ y → ∃ (λ y₀ → thin {n} x y₀ ≡ y)
thin-solve zero zero neq = ⊥-elim (neq refl)
thin-solve zero (suc y₀) neq = y₀ , refl
thin-solve {zero} (suc ()) _ neq
thin-solve {suc n} (suc x) zero neq = zero , refl
thin-solve {suc n} (suc x) (suc y) neq with thin-solve x y (neq ∘ cong suc)
thin-solve {suc n} (suc x) (suc y) neq | y₀′ , eq = suc y₀′ , cong suc eq

open import Data.Maybe
open import MaybeExtras

thick-nofix : ∀ {n} x → thick {n} x x ≡ nothing
thick-nofix zero = refl
thick-nofix {zero} (suc ())
thick-nofix {suc n} (suc x) with thick x x | inspect (thick x) x
thick-nofix {suc n} (suc x) | just _  | [ eq ] = ⊥-elim (just≢nothing (sym eq ⟨ trans ⟩ thick-nofix x))
thick-nofix {suc n} (suc x) | nothing | [ eq ] = refl

thick-thin : ∀ {n} x y → Partial (y ≡ x) (λ y′ → y ≡ thin x y′) (thick {n} x y)
thick-thin zero zero = Nothing refl
thick-thin zero (suc y) = Just refl
thick-thin {zero} (suc ()) _
thick-thin {suc n} (suc x) zero = Just refl
thick-thin {suc n} (suc x) (suc y) with thick x y | inspect (thick x) y
thick-thin {suc n} (suc x) (suc y) | just y′ | [ eq ] = Just (cong suc (Partial-Just (subst (Partial _ _) eq (thick-thin x y))))
thick-thin {suc n} (suc x) (suc y) | nothing | [ eq ] = Nothing (cong suc (Partial-Nothing (subst (Partial _ _) eq (thick-thin x y))))

open import Level using () renaming (zero to ℓ₀)
open import Category.Functor
open RawFunctor {ℓ₀} functor

thick-inv : ∀ {n} x y → thick {n} x (thin x y) ≡ just y
thick-inv zero y = refl
thick-inv (suc x) zero = refl
thick-inv (suc x) (suc y) = cong (_<$>_ suc) (thick-inv x y)
