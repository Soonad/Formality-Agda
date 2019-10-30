module Nat where
open import Logic
open import Equality

-- Natural number
data Nat : Set where
  succ : Nat -> Nat
  zero : Nat
{-# BUILTIN NATURAL Nat #-}

-- Nat addition
_+_ : Nat -> Nat -> Nat
_+_ (succ n) m = succ (_+_ n m)
_+_ zero     m = m
{-# BUILTIN NATPLUS _+_ #-}

-- Nat subtraction
_-_ : Nat -> Nat -> Nat
succ n - succ m = n - m
zero   - succ m = zero
n      - zero   = n
{-# BUILTIN NATMINUS _-_ #-}

-- Nat multiplication
_*_ : Nat -> Nat -> Nat
_*_ (succ n) m = m + (n * m)
_*_ zero     m = zero
{-# BUILTIN NATTIMES _*_ #-}

-- Nat comparison
same : Nat -> Nat -> Bool
same zero     zero     = true
same zero     (succ m) = false
same (succ n) zero     = false
same (succ n) (succ m) = same n m
{-# BUILTIN NATEQUALS same #-}

-- Less-than-or-equal
data _<=_ : (a : Nat) → (b : Nat) → Set where
  <=zero : ∀ a → 0 <= a
  <=succ : ∀ {a b} → a <= b → succ a <= succ b 

-- Less-than
data _<_ : (a : Nat) → (b : Nat) → Set where
  <zero : ∀ a → 0 < succ a
  <succ : ∀ {a b} → a < b → succ a < succ b 

-- Properties of natural numbers
-- A number added to 0 is the same number
add-n-0 : ∀ n → (n + 0) == n
add-n-0 (succ n) = cong succ (add-n-0 n)
add-n-0 zero     = refl
