module ThinThick where

open import Data.Nat
open import Data.Fin

thin : {n : ℕ} → (x : Fin (suc n)) → Fin n → Fin (suc n)
thin zero    y       = suc y
thin (suc x) zero    = zero
thin (suc x) (suc y) = suc (thin x y)

open import Data.Maybe
open import Level using () renaming (zero to ℓ₀)
open import Category.Functor
open RawFunctor {ℓ₀} functor

thick : {n : ℕ} → (x y : Fin (suc n)) → Maybe (Fin n)
thick zero zero               = nothing
thick zero (suc j)            = just j
thick {zero} (suc ()) y
thick {suc n} (suc i) zero    = just zero
thick {suc n} (suc i) (suc j) = suc <$> thick i j
