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
_+_ 0     m = m
{-# BUILTIN NATPLUS _+_ #-}

-- Nat subtraction
_-_ : Nat -> Nat -> Nat
succ n - succ m = n - m
0   - succ m = 0
n      - 0   = n
{-# BUILTIN NATMINUS _-_ #-}

-- Nat multiplication
_*_ : Nat -> Nat -> Nat
_*_ (succ n) m = m + (n * m)
_*_ 0     m = 0
{-# BUILTIN NATTIMES _*_ #-}

-- Successor is injective
pred : Nat -> Nat
pred 0 = 0
pred (succ n) = n

succ-inj : {a b : Nat} -> (succ a) == (succ b) -> a == b
succ-inj eq = cong pred eq 

succ-inj' : {a b : Nat} -> Not(a == b) -> Not((succ a) == (succ b))
succ-inj' = modus-tollens succ-inj

-- Nat equality is decidable
succ-not-0 : {a : Nat} -> ((succ a) == 0) -> Empty
succ-not-0 ()

==dec : (a b : Nat) -> Or (a == b) (Not (a == b))
==dec 0 0 = or0 refl
==dec (succ a) 0 = or1 succ-not-0
==dec 0 (succ b) = or1 (λ eq -> succ-not-0 (sym eq))
==dec (succ a) (succ b) = case-or (==dec a b) (λ x -> or0 (cong succ x)) (λ x -> or1 (succ-inj' x))

-- Nat comparison
same : Nat -> Nat -> Bool
same 0     0     = true
same 0     (succ m) = false
same (succ n) 0     = false
same (succ n) (succ m) = same n m
{-# BUILTIN NATEQUALS same #-}

-- Arithmetic properties
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
add-assoc 0 b c = refl
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

-- Neutral elements
add-uniq-neutral : (a b : Nat) -> Or ((a + b) == a) ((b + a) == a) -> b == 0
add-uniq-neutral 0 b (or0 eq) = eq
add-uniq-neutral 0 b (or1 eq) = trans (sym (add-n-0 b)) eq
add-uniq-neutral (succ a) b (or0 eq) = add-uniq-neutral a b (or0 (succ-inj eq))
add-uniq-neutral (succ a) b (or1 eq) = add-uniq-neutral a b (or1 (succ-inj (trans (sym (add-n-succ b a)) eq)))

add-no-inverse : (a b : Nat) -> (a + b) == 0 -> And (a == 0) (b == 0)
add-no-inverse 0     0     eq = and refl refl
add-no-inverse 0     (succ b) ()
add-no-inverse (succ a) _        ()

-- Less-than-or-equal
data _<=_ : (a b : Nat) → Set where
  <=zero : ∀ a → 0 <= a
  <=succ : ∀ {a b} → a <= b → succ a <= succ b 

-- Alternative definition
_<='_ : (a b : Nat) -> Set 
a <=' b = Sum Nat (λ (x : Nat) -> (a + x) == b)

lte'->lte : (a b : Nat) -> a <=' b -> a <= b
lte'->lte 0 b _ = <=zero b
lte'->lte (succ a) (succ b) (sigma x eq) = <=succ (lte'->lte a b (sigma x (succ-inj eq)))

lte->lte' : (a b : Nat) -> a <= b -> a <=' b
lte->lte' 0 b _ = sigma b refl
lte->lte' (succ a) (succ b) (<=succ pf) =
  let sigma x pf = (lte->lte' a b pf)
  in sigma x (cong succ pf)

lte-right-wit : {a b : Nat} (x : Nat) -> (a + x) == b -> a <= b
lte-right-wit {a} {b} x eq = lte'->lte a b (sigma x eq)

lte-left-wit : {a b : Nat} (x : Nat) -> (x + a) == b -> a <= b
lte-left-wit {a} {b} x eq = lte'->lte a b (sigma x (trans (add-comm a x) eq))

-- Less-than-or-equal properties
lte-refl : {a b : Nat} -> a == b -> a <= b
lte-refl {0} {0} _ = <=zero 0
lte-refl {succ a} {succ b} eq = <=succ (lte-refl (succ-inj eq))

lte-trans : {a b c : Nat} -> a <= b -> b <= c -> a <= c
lte-trans {a} {b} {c} (<=zero b) _ = (<=zero c)
lte-trans (<=succ pfa) (<=succ pfb) = <=succ (lte-trans pfa pfb)

lte-antisym : {a b : Nat} -> a <= b -> b <= a -> a == b
lte-antisym (<=zero 0) (<=zero 0) = refl
lte-antisym (<=succ pfa) (<=succ pfb) = cong succ (lte-antisym pfa pfb)

lte-total : (a b : Nat) -> Or (a <= b) (b <= a)
lte-total 0 b = or0 (<=zero b)
lte-total a 0 = or1 (<=zero a)
lte-total (succ a) (succ b) = case-or (lte-total a b) (λ x -> or0 (<=succ x)) (λ x -> or1 (<=succ x))

succ-not-lte-0 : {a : Nat} -> Not ((succ a) <= 0) 
succ-not-lte-0 ()

succ-strict : {a b : Nat} -> (succ a) <= (succ b) -> a <= b
succ-strict (<=succ pf) = pf

lte-dec : (a b : Nat) -> Or (a <= b) (Not (a <= b))
lte-dec zero b = or0 (<=zero b)
lte-dec (succ a) zero = or1 succ-not-lte-0
lte-dec (succ a) (succ b) = case-or (lte-dec a b) (λ x -> or0 (<=succ x)) (λ x -> or1 (λ pf -> x (succ-strict pf)))

lte-bottom : {a : Nat} -> a <= 0 -> a == 0
lte-bottom {0} (<=zero 0) = refl

-- Less-than
data _<_ : (a : Nat) → (b : Nat) → Set where
  <zero : ∀ a → 0 < succ a
  <succ : ∀ {a b} → a < b → succ a < succ b 

lt->lte : {a b : Nat} -> a < b -> a <= b
lt->lte {0} {(succ b)} (<zero b) = <=zero (succ b)
lt->lte {succ a} {succ b} (<succ pf) = <=succ (lt->lte pf)

lte=lt-or-eq : (a b : Nat) -> a <= b -> Or (a < b) (a == b)
lte=lt-or-eq zero zero _ = or1 refl
lte=lt-or-eq zero (succ b) _ = or0 (<zero b)
lte=lt-or-eq (succ a) (succ b) (<=succ pf) = case-or (lte=lt-or-eq a b pf) (λ x -> or0 (<succ x)) (λ x -> or1 (cong succ x))

-- postulate
--   sub-fct0 : ∀ a b c d → ((a - b) + (c - d)) == ((a + c) - (b + d))
--   <dist    : ∀ {a b c d} → a < b → c < d → (a + c) < (b + d)
--   <=dist   : ∀ {a b c d} → a <= b → c <= d → (a + c) <= (b + d)
--   <<=dist  : ∀ {a b c d} → a < b → c <= d → (a + c) < (b + d)
--   <=<dist  : ∀ {a b c d} → a <= b → c < d → (a + c) < (b + d)
--   <=fct0   : ∀ {a b c0 c1 d} → c0 <= c1 → a <= (b + (c0 * d)) → a <= (b + (c1 * d))
--   <=fct1   : ∀ {a b0 b1 c} → b0 <= b1 → a <= (b0 + c) → a <= (b1 + c)
--   <=fct2   : ∀ {a b c0 c1} → c0 <= c1 → a <= (b + c0) → a <= (b + c1)
--   <=tran   : ∀ {a b c} → a <= b → b <= c → a <= c
--   <=addr   : ∀ {a b} → (x : Nat) → a <= b → a <= (b + x)
--   <=incr   : ∀ {a b} → a <= b → a <= succ b
--   <=-to-<  : ∀ {a b} → a <= b → a < succ b
