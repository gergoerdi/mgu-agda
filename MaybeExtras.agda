module MaybeExtras where

open import Data.Maybe

open import Relation.Binary.Core
open import Relation.Nullary
open import Data.Empty

just≢nothing : ∀ {a} {A : Set a} {x : A} → ¬ (_≡_ {A = Maybe A} (just x) nothing)
just≢nothing ()

just-inv : ∀ {a} {A : Set a} {x y : A} → (_≡_ {A = Maybe A} (just x) (just y)) → x ≡ y
just-inv refl = refl

data Partial {A : Set} (P : A → Set) (Q : Set) : Maybe A → Set where
  Just : ∀ {x} → P x → Partial P Q (just x)
  Nothing : Q → Partial P Q nothing

Partial-Just : ∀ {A P Q x} → Partial {A} P Q (just x) → P x
Partial-Just (Just P) = P

Partial-Nothing : ∀ {A P Q} → Partial {A} P Q nothing → Q
Partial-Nothing (Nothing Q) = Q
