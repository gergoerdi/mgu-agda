module S where

-- https://github.com/wjzz/agda-DTP-examples/blob/master/Unification/Unification.agda

open import Data.Nat
open import Data.Fin
-- open import Data.Fin.Props renaming (_≟_ to _F≟_)
open import Function using (_∘_; _⟨_⟩_; id; flip)

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Empty

open import Data.Maybe
open import Category.Applicative
open import MaybeExtras
open import Level using () renaming (zero to ℓ₀)
open import Category.Monad
open RawMonad {ℓ₀} monad using (_>>=_; return) renaming (rawIApplicative to applicative)
open RawApplicative {ℓ₀} applicative

open import ThinThick

Var : ℕ → Set
Var = Fin

data Term (n : ℕ) : Set where
  leaf   : Term n
  var    : Var n → Term n
  _fork_ : (t u : Term n) → Term n

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

module substitute-Props where
  substitute-id : ∀ {m} → substitute {m} var ≗ id
  substitute-id {m} leaf = refl
  substitute-id {m} (var x) = refl
  substitute-id {m} (t₁ fork t₂) = substitute-id t₁ ⟨ cong₂ _fork_ ⟩ substitute-id t₂

  substitute-≡ : ∀ {m n} {f g : m ⇝ n} → (∀ x → f x ≡ g x) → ∀ t → substitute f t ≡ substitute g t
  substitute-≡ eq leaf = refl
  substitute-≡ eq (var x) = eq x
  substitute-≡ eq (t₁ fork t₂) = substitute-≡ eq t₁ ⟨ cong₂ _fork_ ⟩ substitute-≡ eq t₂

  substitute-leaf : ∀ {m n} {f : m ⇝ n} → leaf ≡ substitute f leaf
  substitute-leaf = refl

  substitute-assoc : ∀ {l m n} (f : m ⇝ n) (g : l ⇝ m) → substitute (substitute f ∘ g) ≗ substitute f ∘ substitute g
  substitute-assoc f g leaf = refl
  substitute-assoc f g (var x) = refl
  substitute-assoc f g (t₁ fork t₂) = substitute-assoc f g t₁ ⟨ cong₂ _fork_ ⟩ substitute-assoc f g t₂

  substitute-rename : ∀ {l m n} → (f : m ⇝ n) (g : Var l → Var m) → substitute f ∘ substitute (rename g) ≗ substitute (f ∘ g)
  substitute-rename f g leaf = refl
  substitute-rename f g (var x) = refl
  substitute-rename f g (t₁ fork t₂) = substitute-rename f g t₁ ⟨ cong₂ _fork_ ⟩ substitute-rename f g t₂

  ◇-assoc : ∀ {k l m n} (f : m ⇝ n) (g : l ⇝ m) (h : k ⇝ l) → (f ◇ g) ◇ h ≗ f ◇ (g ◇ h)
  ◇-assoc f g h x =  substitute-assoc f g (h x)

check : ∀ {n} (x : Var (suc n)) → Term (suc n) → Maybe (Term n)
check x leaf = just leaf
check x (var y) = var <$> thick x y
check x (t₁ fork t₂) = _fork_ <$> check x t₁ ⊛ check x t₂

_for_ : {n : ℕ} → (t : Term n) → (x : Var (suc n)) → (suc n ⇝ n)
(t for x) y = maybe′ var t (thick x y)

module for-Props where
  for-thin : ∀ {n} {t : Term n} {x y} → (t for x) (thin x y) ≡ var y
  for-thin {n} {t} {x} {y} with thick x (thin x y) | inspect (thick x) (thin x y)
  for-thin {n} {t} {x} {y} | just y′ | [ eq ] = cong var (thin-inj x (sym (Partial-Just (subst (Partial _ _) eq (thick-thin x (thin x y))))))
  for-thin {n} {t} {x} {y} | nothing | [ eq ] = ⊥-elim (thin-nofix x (Partial-Nothing (subst (Partial _ _) eq (thick-thin x (thin x y)))))

  for-unify : ∀ {n} x (t : Term (suc n)) {t′ : Term n} → check x t ≡ just t′ →
              substitute (t′ for x) t ≡ (t′ for x) x
  for-unify {n} x t {t′} eq =
    begin
      substitute (t′ for x) t
    ≡⟨ {!!} ⟩
      substitute (t′ for x) (substitute (rename (thin x)) t′)
    ≡⟨ substitute-rename (t′ for x) (thin x) t′ ⟩
      substitute (t′ for x ∘ thin x) t′
    ≡⟨ substitute-≡ (cong (maybe′ var t′) ∘ thick-inv x) t′ ⟩
      substitute var t′
    ≡⟨ substitute-id t′ ⟩
      t′
    ≡⟨ maybe-nothing (thick-nofix x) ⟩
      (t′ for x) x
    ∎
    where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
    open substitute-Props
    maybe-nothing : ∀ {f y mx} → mx ≡ nothing → y ≡ maybe′ f y mx
    maybe-nothing refl = refl

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

module sub-Props where
  open import Data.Star.Properties

  sub-id : ∀ {m} → sub {m} ε ≗ var
  sub-id = λ x → refl

  sub-++ : ∀ {m n l} (σ : l ⇝⋆ m) (ρ : m ⇝⋆ n) → sub (σ ++ ρ) ≗ sub ρ ◇ sub σ
  sub-++ ε ρ y = refl
  sub-++ (t′ / x ◅ σ) ρ y = -- cong {!!} (sub-++ σ ρ {!!})
    begin
      sub (t′ / x ◅ σ ++ ρ) y
    ≡⟨ refl ⟩
      (sub (σ ++ ρ) ◇ (t′ for x)) y
    ≡⟨ {!sub-++!} ⟩
      ((sub ρ ◇ sub σ) ◇ (t′ for x)) y
    ≡⟨ ◇-assoc (sub ρ) (sub σ) (t′ for x) y ⟩
      (sub ρ ◇ (sub σ ◇ (t′ for x))) y
    ∎
    where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
    open substitute-Props

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
