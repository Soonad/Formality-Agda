module Nat where
open import Logic
open import Equality
open import EquationalReasoning

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
add-n-0 0     = refl

-- A number added to a successor is the successor of the sum
add-n-succ : ∀ n m → (n + (succ m)) == succ (n + m)
add-n-succ (succ n) m = cong succ (add-n-succ n m)
add-n-succ 0 m = refl

-- Commutativity of the sum
add-comm : (a b : Nat) -> (a + b) == (b + a)
add-comm 0 b =
  begin
    0 + b
  ==< sym (add-n-0 b) >
    b + 0
  qed
add-comm (succ a) b =
  begin
    (succ a) + b
  ==<>
    succ (a + b)
  ==< cong succ (add-comm a b) >
    succ (b + a)
  ==< sym (add-n-succ b a) >
    b + (succ a)
  qed

-- Associativity of the sum
add-assoc : (a b c : Nat) -> (a + (b + c)) == ((a + b) + c)
add-assoc zero b c = refl
add-assoc (succ a) b c =
  begin
    succ (a + (b + c))
  ==< cong succ (add-assoc a b c) >
    succ ((a + b) + c)
  ==<>
    ((succ a) + b) + c
  qed

add-left-swap : ∀ a b c → (a + (b + c)) == (b + (a + c))
add-left-swap a b c =
  begin
    (a + (b + c))
  ==< add-assoc a b c >
    ((a + b) + c)
  ==< cong (_+ c) (add-comm a b) >
    ((b + a) + c)
  ==< sym (add-assoc b a c) >
    (b + (a + c))
  qed

add-inner-swap : ∀ a b c d → ((a + b) + (c + d)) == ((a + c) + (b + d))
add-inner-swap a b c d =
  begin
    ((a + b) + (c + d))
  ==< sym (add-assoc a b (c + d)) >
    (a + (b + (c + d)))
  ==< cong (a +_) (add-left-swap b c d) >
    (a + (c + (b + d)))
  ==< add-assoc a c (b + d) >
    ((a + c) + (b + d))
  qed

mul-n-0 : (n : Nat) -> (n * 0) == 0
mul-n-0 0 = refl
mul-n-0 (succ n) = mul-n-0 n
 
mul-n-1 : (n : Nat) -> (n * 1) == n
mul-n-1 0 = refl
mul-n-1 (succ n) = cong succ (mul-n-1 n)

mul-n-succ : (n m : Nat) -> (n * (succ m)) == (n + (n * m))
mul-n-succ 0 m = refl
mul-n-succ (succ n) m =
  begin
    (succ n) * (succ m)
  ==<>
    (succ m) + (n * (succ m))
  ==< cong (_+_ (succ m)) (mul-n-succ n m) >
    (succ m) + (n + (n * m))
  ==<>
    succ (m + (n + (n * m)))
  ==< cong succ (add-left-swap m n (n * m)) >
    succ (n + (m + (n * m)))
  ==<>
    ((succ n) + ((succ n) * m))
  qed
 
mul-comm : (a b : Nat) -> (a * b) == (b * a)
mul-comm 0 b = sym (mul-n-0 b)
mul-comm (succ a) b =
  begin
    ((succ a) * b)
  ==<>
    b + (a * b)
  ==< cong (b +_) (mul-comm a b) >
    b + (b * a)
  ==< sym (mul-n-succ b a) >
    (b * (succ a))
  qed

mul-leftdist : (a b c : Nat) -> (a * (b + c)) == ((a * b) + (a * c))
mul-leftdist 0 b c = refl
mul-leftdist (succ a) b c =
  begin
    ((succ a) * (b + c))
  ==<>
    (b + c) + (a * (b + c))
  ==< cong ((b + c) +_) (mul-leftdist a b c) >
    (b + c) + ((a * b) + (a * c))
  ==< (add-inner-swap b c (a * b) (a * c)) >
    ((b + (a * b)) + (c + (a * c)))
  ==<>
    (((succ a) * b) + ((succ a) * c))
  qed

 
mul-rightdist : (a b c : Nat) -> ((a + b) * c) == ((a * c) + (b * c))
mul-rightdist a b c =
  begin
    ((a + b) * c)
  ==< mul-comm (a + b) c >
    (c * (a + b))
  ==< mul-leftdist c a b >
    ((c * a) + (c * b))
  ==< cong ((c * a) +_) (mul-comm c b) >
    ((c * a) + (b * c))
  ==< cong (_+ (b * c)) (mul-comm c a) >
    ((a * c) + (b * c))
  qed

mul-assoc : (a b c : Nat) -> (a * (b * c)) == ((a * b) * c)
mul-assoc 0 b c = refl
mul-assoc (succ a) b c =
  begin
    (succ a) * (b * c)
  ==<>
    (b * c) + (a * (b * c))
  ==< cong ((b * c) +_) (mul-assoc a b c) >
    (b * c) + ((a * b) * c)
  ==< sym (mul-rightdist b (a * b) c) >
    (b + (a * b)) * c
  ==<>
    (((succ a) * b) * c)
  qed
