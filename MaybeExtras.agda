module MaybeExtras where

open import Data.Maybe

open import Relation.Binary.Core
open import Relation.Nullary
open import Data.Empty

just≢nothing : ∀ {a} {A : Set a} {x : A} → ¬ (_≡_ {A = Maybe A} (just x) nothing)
just≢nothing ()

just-inv : ∀ {a} {A : Set a} {x y : A} → (_≡_ {A = Maybe A} (just x) (just y)) → x ≡ y
just-inv refl = refl

data Partial {A : Set} (P : Set) (Q : A → Set) : Maybe A → Set where
  Nothing : P → Partial P Q nothing
  Just : ∀ {x} → Q x → Partial P Q (just x)

Partial-Just : ∀ {A P Q x} → Partial {A} P Q (just x) → Q x
Partial-Just (Just Q) = Q

Partial-Nothing : ∀ {A P Q} → Partial {A} P Q nothing → P
Partial-Nothing (Nothing P) = P

open import Data.Product

force-Just : ∀ {A P Q mx} → ¬ P → Partial {A} P Q mx → ∃ Q
force-Just ¬P (Nothing P) = ⊥-elim (¬P P)
force-Just ¬P (Just {x} Qx) = x , Qx
