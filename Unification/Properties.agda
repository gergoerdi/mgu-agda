module Unification.Properties where

open import Unification

open import Data.Nat
open import Data.Fin
open import Function using (_∘_; _⟨_⟩_; id; flip)

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Empty

open import Data.Maybe

open import ThinThick
open import ThinThick.Properties

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

open import Data.Product

module for-Props where
  for-thin : ∀ {n} {t : Term n} {x y} → (t for x) (thin x y) ≡ var y
  for-thin {n} {t} {x} {y} = maybe-just (thick-inv x y)
    where
    maybe-just : ∀ {f y mx x} → mx ≡ just x → maybe′ f y mx ≡ f x
    maybe-just refl = refl

  check-fork : ∀ {n} x (t₁ t₂ : Term (suc n)) {t′ : Term n} → check x (t₁ fork t₂) ≡ just t′ → ∃ (uncurry λ t₁′ t₂′ → t′ ≡ t₁′ fork t₂′)
  check-fork x leaf leaf {.leaf fork leaf} refl = (leaf , leaf) , refl
  check-fork x leaf (var x₁) {leaf} eq = {!eq!}
  check-fork x leaf (var x₁) {var x₂} eq = {!eq!}
  check-fork x leaf (var x₁) {t′ fork t′₁} eq = {!eq!}
  check-fork x leaf (t₂ fork t₃) eq = {!!}
  check-fork x (var x₁) t₂ eq = {!!}
  check-fork x (t₁ fork t₂) t₃ eq = {!!}

  checkˡ : ∀ {n} x (t₁ t₂ : Term (suc n)) {t′ : Term n} → check x (t₁ fork t₂) ≡ just t′ → ∃ λ t″ → check x t₁ ≡ just t″
  checkˡ x t₁ t₂ eq with check-fork x t₁ t₂ eq | inspect (check-fork x t₁ t₂) eq
  checkˡ x t₁ t₂ eq | (t₁′ , t₂′) , eq′ | [ prf ] = t₁′ , {!!}

  for-unify₀ : ∀ {n} x (t : Term (suc n)) {t′ : Term n} → check x t ≡ just t′ →
               substitute (t′ for x) t ≡ substitute (t′ for x) (substitute (rename (thin x)) t′)
  for-unify₀ x leaf refl = refl
  for-unify₀ x (var y) eq = {!eq!}
  for-unify₀ x (t₁ fork t₂) eq with for-unify₀ x t₁ {!!} | for-unify₀ x t₂ {!!}
  ... | p | q = {!!}

  for-unify : ∀ {n} x (t : Term (suc n)) {t′ : Term n} → check x t ≡ just t′ →
              substitute (t′ for x) t ≡ (t′ for x) x
  for-unify {n} x t {t′} eq =
    begin
      substitute (t′ for x) t
    ≡⟨ for-unify₀ x t eq ⟩
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

open import Data.Star

module sub-Props where
  open import Data.Star.Properties

  sub-id : ∀ {m} → sub {m} ε ≗ var
  sub-id = λ x → refl

  sub-++ : ∀ {m n l} (σ : l ⇝⋆ m) (ρ : m ⇝⋆ n) → sub (σ ++ ρ) ≗ sub ρ ◇ sub σ
  sub-++ ε ρ y = refl
  sub-++ (t′ / x ◅ σ) ρ y =
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
