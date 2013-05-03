module Unification where

open import Data.Nat
open import Data.Fin
-- open import Data.Fin.Props renaming (_≟_ to _F≟_)
open import Function using (_∘_; flip)

Var : ℕ → Set
Var = Fin

data Term (n : ℕ) : Set where
  leaf   : Term n
  var    : Var n → Term n
  _fork_ : (t u : Term n) → Term n

open import Data.Maybe
open import Category.Applicative
open import MaybeExtras
open import Level using () renaming (zero to ℓ₀)
open import Category.Monad
open RawMonad {ℓ₀} monad using (_>>=_; return) renaming (rawIApplicative to applicative)
open RawApplicative {ℓ₀} applicative

open import ThinThick

_⇝_ : ℕ → ℕ → Set
m ⇝ n = Var m → Term n

_⟿_ : ℕ → ℕ → Set
m ⟿ n = Term m → Term n

rename : {m n : ℕ} → (Var m → Var n) → (m ⇝ n)
rename f = var ∘ f

substitute : {m n : ℕ} → (m ⇝ n) → (m ⟿ n)
substitute f (var i)    = f i
substitute f leaf       = leaf
substitute f (t fork u) = (substitute f t) fork (substitute f u)

_◇_ : ∀ {l m n} → (m ⇝ n) → (l ⇝ m) → (l ⇝ n)
f ◇ g = substitute f ∘ g

check : ∀ {n} (x : Var (suc n)) → Term (suc n) → Maybe (Term n)
check x leaf = just leaf
check x (var y) = var <$> thick x y
check x (t₁ fork t₂) = _fork_ <$> check x t₁ ⊛ check x t₂

_for_ : {n : ℕ} → (t : Term n) → (x : Var (suc n)) → (suc n ⇝ n)
(t for x) y = maybe′ var t (thick x y)

open import Data.Star hiding (_>>=_)

data _//_ : ℕ → ℕ → Set where
  _/_ : ∀ {m} → (t′ : Term m) → (x : Var (suc m)) → m // suc m

_⇝⋆_ : (m n : ℕ) → Set
m ⇝⋆ n = Star (flip _//_) m n

sub : ∀ {m n} → (σ : m ⇝⋆ n) → (m ⇝ n)
sub = Data.Star.fold _⇝_ f var
  where
  f : ∀ {l m n : ℕ} → m // l → m ⇝ n → (l ⇝ n)
  f (t′ / x) k = k ◇ (t′ for x)

_++_ : ∀ {l m n} → (σ : l ⇝⋆ m) (ρ : m ⇝⋆ n) → l ⇝⋆ n
_++_ = _◅◅_

open import Data.Product

_⇝⋆□ : ℕ → Set
m ⇝⋆□ = ∃ (_⇝⋆_ m)

_/_◅?_ : ∀ {m} (t′ : Term m) (x : Var (suc m)) (a : m ⇝⋆□) → (suc m ⇝⋆□)
t′ / x ◅? (n , σ) = n , t′ / x ◅ σ

mgu : ∀ {m} (s t : Term m) → Maybe (m ⇝⋆□)
mgu {m} s t = go s t (m , ε)
  where
  flexFlex : ∀ {m} (x y : Var m) → ∃ (_⇝⋆_ m)
  flexFlex {zero} () ()
  flexFlex {suc m} x y = maybe′ (λ y′ → m , var y′ / x ◅ ε) (suc m , ε) (thick x y)

  flexRigid : ∀ {m} (x : Var m) → (t : Term m) → Maybe (∃ (_⇝⋆_ m))
  flexRigid {zero} () t
  flexRigid {suc m} x t = (λ t′ → m , t′ / x ◅ ε) <$> check x t

  go : ∀ {m} (s t : Term m) → (m ⇝⋆□) → Maybe (m ⇝⋆□)
  go leaf         leaf         acc             = just acc
  go leaf         (_ fork _)   acc             = nothing
  go (_ fork _)   leaf         acc             = nothing
  go (s₁ fork s₂) (t₁ fork t₂) acc             = go s₁ t₁ acc >>= go s₂ t₂
  go (var x)      (var y)      (m , ε)         = just (flexFlex x y)
  go (var x)      t            (m , ε)         = flexRigid x t
  go t            (var x)      (m , ε)         = flexRigid x t
  go s            t            (n , r / z ◅ σ) = (λ a → r / z ◅? a) <$> go (substitute (r for z) s) (substitute (r for z) t) (n , σ)
