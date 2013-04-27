module S where

-- https://github.com/wjzz/agda-DTP-examples/blob/master/Unification/Unification.agda

open import Data.Nat
open import Data.Fin
open import Data.Fin.Props renaming (_≟_ to _F≟_)
open import Function using (_∘_; _⟨_⟩_)

thin : {n : ℕ} → (x : Fin (suc n)) → Fin n → Fin (suc n)
thin zero    y       = suc y
thin (suc x) zero    = zero
thin (suc x) (suc y) = suc (thin x y)

open import Algebra.FunctionProperties
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Relation.Nullary
open import Data.Empty

module thin-Props where
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

  thin-solve : ∀ {n} x y → x ≢ y → Σ[ y₀ ∈ _ ](thin {n} x y₀ ≡ y)
  thin-solve zero zero neq = ⊥-elim (neq refl)
  thin-solve zero (suc y₀) neq = y₀ , refl
  thin-solve {zero} (suc ()) _ neq
  thin-solve {suc n} (suc x) zero neq = zero , refl
  thin-solve {suc n} (suc x) (suc y) neq with thin-solve x y (neq ∘ cong suc)
  thin-solve {suc n} (suc x) (suc y) neq | y₀′ , eq = suc y₀′ , cong suc eq

open import Data.Maybe
open import Category.Applicative

module MaybeExtras where
  applicative : ∀ {a} → RawApplicative {a} Maybe
  applicative {a} = record
    { pure = just
    ; _⊛_ = app
    }
    where
      open import Category.Functor
      open RawFunctor {a} Data.Maybe.functor
      app : ∀ {A B} → Maybe (A → B) → Maybe A → Maybe B
      app (just f) mx = f <$> mx
      app nothing mx = nothing

  just≢nothing : ∀ {a} {A : Set a} {x : A} → ¬ (_≡_ {A = Maybe A} (just x) nothing)
  just≢nothing ()

  data Partial {A : Set} (P : A → Set) (Q : Set) : Maybe A → Set where
    Just : ∀ {x} → P x → Partial P Q (just x)
    Nothing : Q → Partial P Q nothing

  Partial-Just : ∀ {A P Q x} → Partial {A} P Q (just x) → P x
  Partial-Just (Just P) = P

  Partial-Nothing : ∀ {A P Q} → Partial {A} P Q nothing → Q
  Partial-Nothing (Nothing Q) = Q

open MaybeExtras
open import Level using () renaming (zero to ℓ₀)
open RawApplicative {ℓ₀} applicative

thick : {n : ℕ} → (x y : Fin (suc n)) → Maybe (Fin n)
thick zero zero               = nothing
thick zero (suc j)            = just j
thick {zero} (suc ()) y
thick {suc n} (suc i) zero    = just zero
thick {suc n} (suc i) (suc j) = suc <$> thick i j

module thick-Props where
  thick-nofix : ∀ {n} x → thick {n} x x ≡ nothing
  thick-nofix zero = refl
  thick-nofix {zero} (suc ())
  thick-nofix {suc n} (suc x) with thick x x | inspect (thick x) x
  thick-nofix {suc n} (suc x) | just _  | [ eq ] = ⊥-elim (just≢nothing (sym eq ⟨ trans ⟩ thick-nofix x))
  thick-nofix {suc n} (suc x) | nothing | [ eq ] = refl

  thick-thin : ∀ {n} x y → Partial (λ y′ → y ≡ thin x y′) (y ≡ x) (thick {n} x y)
  thick-thin zero zero = Nothing refl
  thick-thin zero (suc y) = Just refl
  thick-thin {zero} (suc ()) _
  thick-thin {suc n} (suc x) zero = Just refl
  thick-thin {suc n} (suc x) (suc y) with thick x y | inspect (thick x) y
  thick-thin {suc n} (suc x) (suc y) | just y′ | [ eq ] = Just (cong suc (Partial-Just (subst (Partial _ _) eq (thick-thin x y))))
  thick-thin {suc n} (suc x) (suc y) | nothing | [ eq ] = Nothing (cong suc (Partial-Nothing (subst (Partial _ _) eq (thick-thin x y))))


TV : ℕ → Set
TV = Fin

Con : Set
Con = ℕ

data Type (n : ℕ) : Set where
  TCon : Con → Type n
  TVar : TV n → Type n
  TApp : Type n → Type n → Type n

rename : {n m : ℕ} → (Fin m → Fin n) → (Fin m → Type n)
rename f = TVar ∘ f

substitute : {n m : ℕ} → (Fin n → Type m) → (Type n → Type m)
substitute f (TVar i)    = f i
substitute f (TCon c)    = TCon c
substitute f (TApp t t′) = TApp (substitute f t) (substitute f t′)

-- bind : {n m l : ℕ} → (Fin m → Type n) → (Fin l → Type m) → (Fin l → Type n)
-- bind f g = substitute f ∘ g

occurs-check : ∀ {n} (x : Fin (suc n)) → Type (suc n) → Maybe (Type n)
occurs-check x (TCon c) = just (TCon c)
occurs-check x (TVar y) = TVar <$> thick x y
occurs-check x (TApp t₁ t₂) = TApp <$> occurs-check x t₁ ⊛ occurs-check x t₂

_for_ : {n : ℕ} → (t : Type n) → (x : Fin (suc n)) → Fin (suc n) → Type n
(t for x) y = maybe′ TVar t (thick x y)

module for-Props where
  open thin-Props
  open thick-Props

  for-thin : ∀ {n} {t : Type n} {x y} → (t for x) (thin x y) ≡ TVar y
  for-thin {n} {t} {x} {y} with thick x (thin x y) | inspect (thick x) (thin x y)
  for-thin {n} {t} {x} {y} | just y′ | [ eq ] = cong TVar (thin-inj x (sym (Partial-Just (subst (Partial _ _) eq (thick-thin x (thin x y))))))
  for-thin {n} {t} {x} {y} | nothing | [ eq ] = ⊥-elim (thin-nofix x (Partial-Nothing (subst (Partial _ _) eq (thick-thin x (thin x y)))))

  for-unify : ∀ {n} x (t : Type (suc n)) {t′ : Type n} → occurs-check x t ≡ just t′ →
              substitute (t′ for x) t ≡ (t′ for x) x
  for-unify x t eq = {!!}
