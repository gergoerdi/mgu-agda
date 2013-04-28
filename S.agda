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
open import Category.Monad
open RawMonad {ℓ₀} monad using (_>>=_; return)

open import ThinThick

V : ℕ → Set
V = Fin

data Term (n : ℕ) : Set where
  leaf : Term n
  var : V n → Term n
  app : (t u : Term n) → Term n

rename : {n m : ℕ} → (Fin m → Fin n) → (Fin m → Term n)
rename f = var ∘ f

substitute : {n m : ℕ} → (Fin n → Term m) → (Term n → Term m)
substitute f (var i)    = f i
substitute f leaf       = leaf
substitute f (app t u) = app (substitute f t) (substitute f u)

_◇_ : {n m l : ℕ} → (Fin m → Term n) → (Fin l → Term m) → (Fin l → Term n)
f ◇ g = substitute f ∘ g

occurs-check : ∀ {n} (x : Fin (suc n)) → Term (suc n) → Maybe (Term n)
occurs-check x leaf = just leaf
occurs-check x (var y) = var <$> thick x y
occurs-check x (app t₁ t₂) = app <$> occurs-check x t₁ ⊛ occurs-check x t₂

_for_ : {n : ℕ} → (t : Term n) → (x : Fin (suc n)) → Fin (suc n) → Term n
(t for x) y = maybe′ var t (thick x y)

module for-Props where
  for-thin : ∀ {n} {t : Term n} {x y} → (t for x) (thin x y) ≡ var y
  for-thin {n} {t} {x} {y} with thick x (thin x y) | inspect (thick x) (thin x y)
  for-thin {n} {t} {x} {y} | just y′ | [ eq ] = cong var (thin-inj x (sym (Partial-Just (subst (Partial _ _) eq (thick-thin x (thin x y))))))
  for-thin {n} {t} {x} {y} | nothing | [ eq ] = ⊥-elim (thin-nofix x (Partial-Nothing (subst (Partial _ _) eq (thick-thin x (thin x y)))))

  for-unify : ∀ {n} x (t : Term (suc n)) {t′ : Term n} → occurs-check x t ≡ just t′ →
              substitute (t′ for x) t ≡ (t′ for x) x
  for-unify x leaf eq = just-inv (eq ⟨ trans ⟩ cong just (maybe-nothing (thick-nofix x)))
    where
    maybe-nothing : ∀ {f y mx} → mx ≡ nothing → y ≡ maybe′ f y mx
    maybe-nothing refl = refl
  for-unify x (var y) eq = {!!}
  for-unify x (app t₁ t₂) eq = {!!}

data AList : (m n : ℕ) → Set where
  anil : ∀ {n} → AList n n
  _asnoc_/_ : ∀ {m n} → (σ : AList m n) → (t′ : Term m) → (x : Fin (suc m)) → AList (suc m) n

-- open import Data.Star
-- open import Data.Star.Decoration
-- open import Data.Product

-- AList : (m n : ℕ) → Set
-- AList m n = Data.Star.Decoration.All {I = ℕ × ℕ} {T = T} (λ {m,n} _ → let m = proj₁ m,n in Term m × Fin (suc m)) #m,n -- (Star {I = ℕ} T m n) -- Star {I = ℕ} T m n
--   where
--   T : Rel (ℕ × ℕ) _
--   T (sm , _) (m , _) = sm ≡ suc m

--   #m,n : Star {I = ℕ × ℕ} T {!!} {!!}
--   #m,n = {!!}

-- anil : ∀ {n} → AList n n
-- anil = ε

-- _asnoc_/_ : ∀ {m n} → (σ : AList m n) → (t′ : Term m) → (x : Fin (suc m)) → AList (suc m) n
-- σ asnoc t′ / x = ↦ (t′ , x) ◅ σ

-- ▷_ : ∀ {m n} → (r : Fin m → Fin n) → (Fin m → Term n)
-- ▷_ = rename

-- _◁ : ∀ {m n} → (f : Fin m → Term n) → (Term m → Term n)
-- _◁ = substitute

sub : ∀ {m n} → (σ : AList m n) → Fin m → Term n
sub anil = var
sub (σ asnoc t′ / x) = (sub σ) ◇ (t′ for x)

_++_ : ∀ {m n l} → (ρ : AList m n) → (σ : AList l m) → AList l n
ρ ++ anil = ρ
ρ ++ (σ asnoc t′ / x) = (ρ ++ σ) asnoc t′ / x

sub-++ : ∀ {m n l} (ρ : AList m n) (σ : AList l m) → ∀ y → sub (ρ ++ σ) y ≡ (sub ρ ◇ sub σ) y
sub-++ ρ anil y = refl
sub-++ ρ (σ asnoc t′ / x) y = {!sub-++ ρ σ ?!} -- cong {!!} (sub-++ ρ σ {!!}) -- cong (λ f → (λ y → f (maybe var t′ (thick x y)))) (sub-++ ρ σ)

open import Data.Product

_asnoc′_/_ : ∀ {m} (a : ∃ (AList m)) → (t′ : Term m) → (x : Fin (suc m)) → ∃ (AList (suc m))
(n , σ) asnoc′ t′ / x = n , σ asnoc t′ / x

mgu : ∀ {m} (s t : Term m) → Maybe (∃ (AList m))
mgu {m} s t = go s t (m , anil)
  where
  flexFlex : ∀ {m} (x y : Fin m) → ∃ (AList m)
  flexFlex {zero} () ()
  flexFlex {suc m} x y = maybe′ (λ y′ → m , anil asnoc var y′ / x) (suc m , anil) (thick x y)

  flexRigid : ∀ {m} (x : Fin m) → (t : Term m) → Maybe (∃ (AList m))
  flexRigid {zero} () t
  flexRigid {suc m} x t = (λ t′ → m , anil asnoc t′ / x) <$> occurs-check x t

  go : ∀ {m} (s t : Term m) → ∃ (AList m) → Maybe (∃ (AList m))
  go leaf        leaf        acc                 = just acc
  go leaf        (app t t₁)  acc                 = nothing
  go (app s₁ s₂) leaf        acc                 = nothing
  go (app s₁ s₂) (app t₁ t₂) acc                 = go s₁ t₁ acc >>= go s₂ t₂
  go (var x)     (var y)     (m , anil)          = just (flexFlex x y)
  go (var x)     t           (m , anil)          = flexRigid x t
  go t           (var x)     (m , anil)          = flexRigid x t
  go s           t           (n , σ asnoc r / z) = (λ a → a asnoc′ r / z) <$> go (substitute (r for z) s) (substitute (r for z) t) (n , σ)
