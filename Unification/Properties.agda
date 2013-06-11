module Unification.Properties where

open import Unification

open import Data.Nat
open import Data.Fin
open import Function using (_∘_; _⟨_⟩_; id; flip)

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Empty

open import Data.Maybe
open import MaybeExtras

open import ThinThick
open import ThinThick.Properties

open import Level using () renaming (zero to ℓ₀)
open import Category.Monad
open RawMonad {ℓ₀} monad using (_>>=_; return) renaming (rawIApplicative to applicative)
open import Category.Applicative
open RawApplicative {ℓ₀} applicative

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

  substitute-fork : ∀ {m n} {f : m ⇝ n} {t₁ t₂} {t₁′ t₂′} → t₁′ ≡ substitute f t₁ → t₂′ ≡ substitute f t₂ → t₁′ fork t₂′ ≡ substitute f (t₁ fork t₂)
  substitute-fork eq₁ eq₂ = cong₂ _fork_ eq₁ eq₂

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

  check-fork : ∀ {n} x (t₁ t₂ : Term (suc n)) {t′ : Term n} → check x (t₁ fork t₂) ≡ just t′ → ∃ λ t₁′ → ∃ λ t₂′ → t′ ≡ t₁′ fork t₂′ × check x t₁ ≡ just t₁′ × check x t₂ ≡ just t₂′
  check-fork x t₁ t₂ eq with check x t₁ | check x t₂
  check-fork x t₁ t₂ refl | just t₁′ | just t₂′ = t₁′ , t₂′ , refl , refl , refl
  check-fork x t₁ t₂ () | just x₁ | nothing
  check-fork x t₁ t₂ () | nothing | _

  check-occurs-var : ∀ {n} x (y : Var (suc n)) {t′ : Term n} → check x (var y) ≡ just t′ → y ≢ x
  check-occurs-var x .x eq refl with thick x x | thick-nofix x
  check-occurs-var x .x eq refl | just _ | ()
  check-occurs-var x .x () refl | nothing | _

  -- check-var : ∀ {n} x (y : Var (suc n)) {t′ : Term n} → check x (var y) ≡ just t′ → ∃ λ y′ → t′ ≡ var y′
  -- check-var x y eq with force-Just (check-occurs-var x y eq) (thick-thin x y)
  -- check-var {n} x .(thin x y′) eq | y′ , refl = y′ , just-inv (sym eq ⟨ trans ⟩ lem)
  --   where
  --   lem : var <$> thick x (thin x y′) ≡ just (var y′)
  --   lem =
  --     begin
  --       var <$> thick x (thin x y′)
  --     ≡⟨ cong (λ ξ → var <$> ξ) (thick-inv x y′) ⟩
  --       var <$> just y′
  --     ≡⟨ refl ⟩
  --       just (var y′)
  --     ∎

  check-occurs : ∀ {n} x (t : Term (suc n)) {t′ : Term n} → check x t ≡ just t′ → (t″ t‴ : Term n) → substitute (t″ for x) t ≡ substitute (t‴ for x) t
  check-occurs x leaf eq t″ t‴ = refl
  check-occurs x (var y) eq t″ t‴ with force-Just (check-occurs-var x y eq) (thick-thin x y)
  check-occurs x (var .(thin x y′)) {t′} eq t″ t‴ | y′ , refl =
    begin
      maybe′ var t″ (thick x (thin x y′))
    ≡⟨ cong (maybe′ var t″) (thick-inv x y′) ⟩
      var y′
    ≡⟨ sym (cong (maybe′ var t‴) (thick-inv x y′)) ⟩
      maybe′ var t‴ (thick x (thin x y′))
    ∎
  check-occurs x (t₁ fork t₂) eq t″ t‴ with check-fork x t₁ t₂ eq
  ... | t₁′ , t₂′ , refl , prf₁ , prf₂ = check-occurs x t₁ prf₁ t″ t‴ ⟨ cong₂ _fork_ ⟩ check-occurs x t₂ prf₂ t″ t‴

  check-roundtrip : ∀ {n} x (t : Term (suc n)) {t′ : Term n} → check x t ≡ just t′ →
                  t ≡ substitute (rename (thin x)) t′
  check-roundtrip x leaf refl = refl
  check-roundtrip x (var y) eq with force-Just (check-occurs-var x y eq) (thick-thin x y)
  check-roundtrip x (var .(thin x y′)) {t′} eq | y′ , refl =
    begin
      var (thin x y′)
    ≡⟨ refl ⟩
      substitute (rename (thin x)) (var y′)
    ≡⟨ cong (substitute (rename (thin x))) (just-inv unpack-t′) ⟩
      substitute (rename (thin x)) t′
    ∎
    where
    unpack-t′ : just (var y′) ≡ just t′
    unpack-t′ =
      begin
        just (var y′)
      ≡⟨ refl ⟩
        var <$> just y′
      ≡⟨ cong (λ ξ → var <$> ξ) (sym (thick-inv x y′)) ⟩
        var <$> thick x (thin x y′)
      ≡⟨ eq ⟩
        just t′
      ∎
  check-roundtrip x (t₁ fork t₂) eq with check-fork x t₁ t₂ eq
  ... | t₁′ , t₂′ , refl , prf₁ , prf₂ = check-roundtrip x t₁ prf₁ ⟨ cong₂ _fork_ ⟩ check-roundtrip x t₂ prf₂

  for-unify : ∀ {n} x (t : Term (suc n)) {t′ : Term n} → check x t ≡ just t′ →
              substitute (t′ for x) t ≡ (t′ for x) x
  for-unify {n} x t {t′} eq =
    begin
      substitute (t′ for x) t
    ≡⟨ cong (substitute (t′ for x)) (check-roundtrip x t eq) ⟩
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
    open substitute-Props
    maybe-nothing : ∀ {f y mx} → mx ≡ nothing → y ≡ maybe′ f y mx
    maybe-nothing refl = refl

open import Data.Star

module sub-Props where
  open import Data.Star.Properties

  sub-id : ∀ {m} → sub {m} ε ≗ var
  sub-id = λ _ → refl

  sub-++ : ∀ {m n l} (σ : l ⇝⋆ m) (ρ : m ⇝⋆ n) → sub (σ ++ ρ) ≗ sub ρ ◇ sub σ
  sub-++ ε ρ y = refl
  sub-++ (t′ / x ◅ σ) ρ y =
    begin
      sub (t′ / x ◅ σ ++ ρ) y
    ≡⟨ refl ⟩
      (sub (σ ++ ρ) ◇ (t′ for x)) y
    ≡⟨ refl ⟩
      substitute (sub (σ ++ ρ)) ((t′ for x) y)
    ≡⟨ substitute-≗ (sub-++ σ ρ) ((t′ for x) y) ⟩
      substitute (sub ρ ◇ sub σ) ((t′ for x) y)
    ≡⟨ ◇-assoc (sub ρ) (sub σ) (t′ for x) y ⟩
      (sub ρ ◇ (sub σ ◇ (t′ for x))) y
    ∎
    where
    open substitute-Props
