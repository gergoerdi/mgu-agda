module Unification.Properties where

open import Unification

open import Data.Nat
open import Data.Fin
open import Function using (_∘_; _⟨_⟩_; id; flip)

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Empty

open import Data.Maybe
open import MaybeExtras

open import ThinThick
open import ThinThick.Properties

module substitute-Props where
  substitute-id : ∀ {m} → substitute {m} var ≗ id
  substitute-id {m} leaf = refl
  substitute-id {m} (var x) = refl
  substitute-id {m} (t₁ fork t₂) = substitute-id t₁ ⟨ cong₂ _fork_ ⟩ substitute-id t₂

  substitute-≗ : ∀ {m n} {f g : m ⇝ n} → f ≗ g → substitute f ≗ substitute g
  substitute-≗ eq leaf = refl
  substitute-≗ eq (var x) = eq x
  substitute-≗ eq (t₁ fork t₂) = substitute-≗ eq t₁ ⟨ cong₂ _fork_ ⟩ substitute-≗ eq t₂

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

  check-fork : ∀ {n} x (t₁ t₂ : Term (suc n)) {t′ : Term n} → check x (t₁ fork t₂) ≡ just t′ → ∃ (uncurry λ t₁′ t₂′ → t₁′ fork t₂′ ≡ t′)
  check-fork x t₁ t₂ eq with check x t₁ | check x t₂
  check-fork x t₁ t₂ refl | just t₁′ | just t₂′ = (t₁′ , t₂′) , refl
  check-fork x t₁ t₂ () | just t₁′ | nothing
  check-fork x t₁ t₂ () | nothing | p2

  checkˡ : ∀ {n} x (t₁ t₂ : Term (suc n)) {t′ : Term n} → check x (t₁ fork t₂) ≡ just t′ → ∃ λ t″ → check x t₁ ≡ just t″
  checkˡ x t₁ t₂ eq with check x t₁ | check x t₂
  checkˡ x t₁ t₂ eq | just t₁′ | just t₂′ = t₁′ , refl
  checkˡ x t₁ t₂ () | just x₁ | nothing
  checkˡ x t₁ t₂ () | nothing | q

  checkʳ : ∀ {n} x (t₁ t₂ : Term (suc n)) {t′ : Term n} → check x (t₁ fork t₂) ≡ just t′ → ∃ λ t″ → check x t₂ ≡ just t″
  checkʳ x t₁ t₂ eq with check x t₁ | check x t₂
  checkʳ x t₁ t₂ eq | just t₁′ | just t₂′ = t₂′ , refl
  checkʳ x t₁ t₂ () | just x₁ | nothing
  checkʳ x t₁ t₂ () | nothing | q

  for-unify₀ : ∀ {n} x (t : Term (suc n)) {t′ : Term n} → check x t ≡ just t′ →
               substitute (t′ for x) t ≡ substitute (t′ for x) (substitute (rename (thin x)) t′)
  for-unify₀ x leaf refl = refl
  for-unify₀ x (var y) eq = {!eq!}
  for-unify₀ x (t₁ fork t₂) eq with check-fork x t₁ t₂ eq
  for-unify₀ x (t₁ fork t₂) {.t₁′ fork .t₂′} eq | (t₁′ , t₂′) , refl = {!!}
    -- begin
    --   substitute ((t₁′ fork t₂′) for x) t₁ fork substitute ((t₁′ fork t₂′) for x) t₂
    -- ≡⟨ for-unify₀ x t₁ {!!} ⟨ cong₂ _fork_ ⟩ for-unify₀ x t₂ {!!} ⟩
    --   {!!}
    -- ≡⟨ {!!} ⟩
    --   {!!}
    -- ∎
    -- where
    -- open Relation.Binary.PropositionalEquality.≡-Reasoning
  -- for-unify₀ x (t₁ fork t₂) eq with checkˡ x t₁ t₂ eq | checkʳ x t₁ t₂ eq
  -- for-unify₀ x (t₁ fork t₂) {t′} eq | t₁′ , eq₁ | t₂′ , eq₂ = {!t′!}
  -- for-unify₀ x (t₁ fork t₂) {t′} eq | t₁′ , eq₁ | t₂′ , eq₂ with for-unify₀ x t₁ eq₁ | for-unify₀ x t₂ eq₂
  -- ... | p | q =
  --   begin
  --     substitute (t′ for x) t₁ fork substitute (t′ for x) t₂
  --   ≡⟨ {!p!} ⟨ cong₂ _fork_ ⟩ {!!} ⟩
  --     {!!}
  --   ≡⟨ {!!} ⟩
  --     {!!}
  --   ∎
  --   where
  --   open Relation.Binary.PropositionalEquality.≡-Reasoning

  for-unify : ∀ {n} x (t : Term (suc n)) {t′ : Term n} → check x t ≡ just t′ →
              substitute (t′ for x) t ≡ (t′ for x) x
  for-unify {n} x t {t′} eq =
    begin
      substitute (t′ for x) t
    ≡⟨ for-unify₀ x t eq ⟩
      substitute (t′ for x) (substitute (rename (thin x)) t′)
    ≡⟨ substitute-rename (t′ for x) (thin x) t′ ⟩
      substitute (t′ for x ∘ thin x) t′
    ≡⟨ substitute-≗ (cong (maybe′ var t′) ∘ thick-inv x) t′ ⟩
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
