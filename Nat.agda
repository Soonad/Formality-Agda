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
  ==[ sym (add-n-0 b) ]
    b + 0
  qed
add-comm (succ a) b =
  begin
    (succ a) + b
  ==[]
    succ (a + b)
  ==[ cong succ (add-comm a b) ]
    succ (b + a)
  ==[ sym (add-n-succ b a) ]
    b + (succ a)
  qed

-- Associativity of the sum
add-assoc : (a b c : Nat) -> (a + (b + c)) == ((a + b) + c)
add-assoc 0 b c = refl
add-assoc (succ a) b c =
  begin
    succ (a + (b + c))
  ==[ cong succ (add-assoc a b c) ]
    succ ((a + b) + c)
  ==[]
    ((succ a) + b) + c
  qed

add-left-swap : ∀ a b c → (a + (b + c)) == (b + (a + c))
add-left-swap a b c =
  begin
    (a + (b + c))
  ==[ add-assoc a b c ]
    ((a + b) + c)
  ==[ cong (_+ c) (add-comm a b) ]
    ((b + a) + c)
  ==[ sym (add-assoc b a c) ]
    (b + (a + c))
  qed

add-inner-swap : ∀ a b c d → ((a + b) + (c + d)) == ((a + c) + (b + d))
add-inner-swap a b c d =
  begin
    ((a + b) + (c + d))
  ==[ sym (add-assoc a b (c + d)) ]
    (a + (b + (c + d)))
  ==[ cong (a +_) (add-left-swap b c d) ]
    (a + (c + (b + d)))
  ==[ add-assoc a c (b + d) ]
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
  ==[]
    (succ m) + (n * (succ m))
  ==[ cong (_+_ (succ m)) (mul-n-succ n m) ]
    (succ m) + (n + (n * m))
  ==[]
    succ (m + (n + (n * m)))
  ==[ cong succ (add-left-swap m n (n * m)) ]
    succ (n + (m + (n * m)))
  ==[]
    ((succ n) + ((succ n) * m))
  qed
 
mul-comm : (a b : Nat) -> (a * b) == (b * a)
mul-comm 0 b = sym (mul-n-0 b)
mul-comm (succ a) b =
  begin
    ((succ a) * b)
  ==[]
    b + (a * b)
  ==[ cong (b +_) (mul-comm a b) ]
    b + (b * a)
  ==[ sym (mul-n-succ b a) ]
    (b * (succ a))
  qed

mul-leftdist : (a b c : Nat) -> (a * (b + c)) == ((a * b) + (a * c))
mul-leftdist 0 b c = refl
mul-leftdist (succ a) b c =
  begin
    ((succ a) * (b + c))
  ==[]
    (b + c) + (a * (b + c))
  ==[ cong ((b + c) +_) (mul-leftdist a b c) ]
    (b + c) + ((a * b) + (a * c))
  ==[ (add-inner-swap b c (a * b) (a * c)) ]
    ((b + (a * b)) + (c + (a * c)))
  ==[]
    (((succ a) * b) + ((succ a) * c))
  qed

 
mul-rightdist : (a b c : Nat) -> ((a + b) * c) == ((a * c) + (b * c))
mul-rightdist a b c =
  begin
    ((a + b) * c)
  ==[ mul-comm (a + b) c ]
    (c * (a + b))
  ==[ mul-leftdist c a b ]
    ((c * a) + (c * b))
  ==[ cong ((c * a) +_) (mul-comm c b) ]
    ((c * a) + (b * c))
  ==[ cong (_+ (b * c)) (mul-comm c a) ]
    ((a * c) + (b * c))
  qed

mul-assoc : (a b c : Nat) -> (a * (b * c)) == ((a * b) * c)
mul-assoc 0 b c = refl
mul-assoc (succ a) b c =
  begin
    (succ a) * (b * c)
  ==[]
    (b * c) + (a * (b * c))
  ==[ cong ((b * c) +_) (mul-assoc a b c) ]
    (b * c) + ((a * b) * c)
  ==[ sym (mul-rightdist b (a * b) c) ]
    (b + (a * b)) * c
  ==[]
    (((succ a) * b) * c)
  qed


mul-left-swap : ∀ a b c → (a * (b * c)) == (b * (a * c))
mul-left-swap a b c =
  begin
    (a * (b * c))
  ==[ mul-assoc a b c ]
    ((a * b) * c)
  ==[ cong (_* c) (mul-comm a b) ]
    ((b * a) * c)
  ==[ sym (mul-assoc b a c) ]
    (b * (a * c))
  qed

mul-inner-swap : ∀ a b c d → ((a * b) * (c * d)) == ((a * c) * (b * d))
mul-inner-swap a b c d =
  begin
    ((a * b) * (c * d))
  ==[ sym (mul-assoc a b (c * d)) ]
    (a * (b * (c * d)))
  ==[ cong (a *_) (mul-left-swap b c d) ]
    (a * (c * (b * d)))
  ==[ mul-assoc a c (b * d) ]
    ((a * c) * (b * d))
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

-- An alternative definition of `a <= b` which is really useful is `exists x : Nat, a + x = b` therefore we can write the following functions:
<=-add-get : {a b : Nat} -> a <= b -> Sum Nat (λ (x : Nat) -> (a + x) == b)
<=-add-get {0} {b} _ = sigma b refl
<=-add-get {succ a} {succ b} (<=succ pf) =
  let sigma x pf = (<=-add-get pf)
  in sigma x (cong succ pf)

<=-add : {a b : Nat} (x : Nat) -> (a + x) == b -> a <= b
<=-add {0} {b} _ _ = <=zero b
<=-add {succ a} {succ b} x eq = <=succ (<=-add x (succ-inj eq))

-- Less-than-or-equal properties
<=-refl : {a b : Nat} -> a == b -> a <= b
<=-refl {0} {0} _ = <=zero 0
<=-refl {succ a} {succ b} eq = <=succ (<=-refl (succ-inj eq))

<=-refl' : {a : Nat} -> a <= a
<=-refl' = <=-refl refl

<=-trans : {a b c : Nat} -> a <= b -> b <= c -> a <= c
<=-trans {a} {b} {c} (<=zero b) _ = (<=zero c)
<=-trans (<=succ pfa) (<=succ pfb) = <=succ (<=-trans pfa pfb)

<=-antisym : {a b : Nat} -> a <= b -> b <= a -> a == b
<=-antisym (<=zero 0) (<=zero 0) = refl
<=-antisym (<=succ pfa) (<=succ pfb) = cong succ (<=-antisym pfa pfb)

<=-total : (a b : Nat) -> Or (a <= b) (succ b <= a)
<=-total 0 b = or0 (<=zero b)
<=-total (succ a) 0 = or1 (<=succ (<=zero a))
<=-total (succ a) (succ b) = case-or (<=-total a b) (λ x -> or0 (<=succ x)) (λ x -> or1 (<=succ x))

succ-not-<=-0 : {a : Nat} -> Not ((succ a) <= 0) 
succ-not-<=-0 ()

succ-strict : {a b : Nat} -> (succ a) <= (succ b) -> a <= b
succ-strict (<=succ pf) = pf

<=-dec : (a b : Nat) -> Or (a <= b) (Not (a <= b))
<=-dec zero b = or0 (<=zero b)
<=-dec (succ a) zero = or1 succ-not-<=-0
<=-dec (succ a) (succ b) = case-or (<=-dec a b) (λ x -> or0 (<=succ x)) (λ x -> or1 (λ pf -> x (succ-strict pf)))

<=-bottom : {a : Nat} -> a <= 0 -> a == 0
<=-bottom {0} (<=zero 0) = refl

-- Less-than-or-equal-to Reasoning
infix  1 begin<=_
infixr 2 _<=[_]_
infix  3 _qed<=

begin<=_ : ∀ {x y : Nat}
  → x <= y
    -----
  → x <= y
begin<= x<=y  =  x<=y

_<=[_]_ : ∀ (x : Nat) {y z : Nat}
  → x <= y
  → y <= z
    -----
  → x <= z
x <=[ x<=y ] y<=z  =  <=-trans x<=y y<=z

_qed<= : ∀ (x : Nat)
    -----
  → x <= x
x qed<=  =  <=-refl'

-- Less-than
data _<_ : (a : Nat) → (b : Nat) → Set where
  <zero : ∀ a → 0 < succ a
  <succ : ∀ {a b} → a < b → succ a < succ b 

n-<-succ : {n : Nat} -> n < succ(n)
n-<-succ {0} = <zero 0
n-<-succ {succ n} = <succ n-<-succ

not-n-<-0 : {n : Nat} -> n < 0 -> Empty
not-n-<-0 ()

<-to-<= : {a b : Nat} -> a < b -> (succ a) <= b
<-to-<= {0} {(succ b)} (<zero b) = <=succ (<=zero b)
<-to-<= {succ a} {succ b} (<succ pf) = <=succ (<-to-<= pf)

<-to-<=' : {a b : Nat} -> a < (succ b) -> a <= b
<-to-<=' {0} {b} (<zero b) = <=zero b
<-to-<=' {succ a} {succ b} (<succ pf) = <=succ (<-to-<=' pf)

<=-to-< : {a b : Nat} -> (succ a) <= b -> a < b
<=-to-< {zero} {succ b} _ = <zero b
<=-to-< {succ a} {succ b} (<=succ pf) = <succ (<=-to-< pf)

<=-to-<' : {a b : Nat} -> a <= b -> a < (succ b)
<=-to-<' {zero} {b} _ = <zero b
<=-to-<' {succ a} {succ b} (<=succ pf) = <succ (<=-to-<' pf)

<=-is-<-or-== : {a b : Nat} -> a <= b -> Or (a < b) (a == b)
<=-is-<-or-== {zero}   {zero}   _           = or1 refl
<=-is-<-or-== {zero}   {succ b} _           = or0 (<zero b)
<=-is-<-or-== {succ a} {succ b} (<=succ pf) = case-or (<=-is-<-or-== pf) (λ x -> or0 (<succ x)) (λ x -> or1 (cong succ x))

<-stronger-<= : {a b : Nat} -> a < b -> a <= b
<-stronger-<= {0} {(succ b)} (<zero b) = <=zero (succ b)
<-stronger-<= {succ a} {succ b} (<succ pf) = <=succ (<-stronger-<= pf)

-- An alternative definition of `a < b` is, similarly, is `exists x : Nat, succ (a + x) = b` therefore we can write the following functions:
<-add : {a b : Nat} (x : Nat) -> succ (a + x) == b -> a < b
<-add x eq = <=-to-< (<=-add x eq)

<-add-get : {a b : Nat} -> a < b -> Sum Nat (λ (x : Nat) -> succ (a + x) == b)
<-add-get pf = <=-add-get (<-to-<= pf)

-- Yet another alternative definition of `a < b` is `not (b <= a)`
<-to-not->= : {a b : Nat} -> a < b -> Not(b <= a)
<-to-not->= {succ a} {succ b} (<succ pf1) pf2 = <-to-not->= pf1 (succ-strict pf2) -- all other cases are inconsistent

not->=-to-< : {a b : Nat} -> Not(b <= a) -> a < b
not->=-to-< {a} {zero} neg = absurd (neg (<=zero a))
not->=-to-< {zero} {succ b} _ = <zero b
not->=-to-< {succ a} {succ b} neg = <succ (not->=-to-< (λ (pf : b <= a) -> neg (<=succ pf)))

<-comb-<= : {a b c : Nat} -> a < b -> b <= c -> a < c
<-comb-<= {a} {b} {c} a<b b<=c = let
  sigma x 1+a+x==b = <-add-get a<b
  sigma y b+y==c = <=-add-get b<=c
  eq =
    begin
      succ (a + (x + y))
    ==[ cong succ (add-assoc a x y) ]
      succ ((a + x) + y)
    ==[ cong (_+ y) 1+a+x==b ]
      b + y
    ==[ b+y==c ]
      c
    qed
  in <-add (x + y) eq

<=-comb-< : {a b c : Nat} -> a <= b -> b < c -> a < c
<=-comb-< {a} {b} {c} a<=b b<c = let
  sigma x a+x==b = <=-add-get a<=b
  sigma y 1+b+y==c = <-add-get b<c
  eq =
    begin
      succ (a + (x + y))
    ==[ cong succ (add-assoc a x y) ]
      succ ((a + x) + y)
    ==[ cong (λ x -> succ (x + y)) a+x==b ]
      succ (b + y)
    ==[ 1+b+y==c ]
      c
    qed
  in <-add (x + y) eq

-- Less-than Reasoning: requires proving only one < statement in the whole reasoning chain. The rest can be proven by weaker <= statements
infix  1 begin<_
infixr 2 _<[_]_ _<='[_]_
infix  3 _qed<

begin<_ : ∀ {x y : Nat}
  → x < y
    -----
  → x < y
begin< x<y  =  x<y

_<[_]_ : ∀ (x : Nat) {y z : Nat}
  → x < y
  → y <= z
    -----
  → x < z
x <[ x<y ] y<=z =  <-comb-<= x<y y<=z

_<='[_]_ : ∀ (x : Nat) {y z : Nat}
  → x <= y
  → y < z
    -----
  → x < z
x <='[ x<=y ] y<z =  <=-comb-< x<=y y<z

_qed< : ∀ (x : Nat)
    -----
  → x <= x
x qed<  =  <=-refl'

-- Equational properties
<=-additive : ∀ {a b c d}
          → a <= b
          → c <= d
          --------------------
          → (a + c) <= (b + d)
<=-additive {a} {b} {c} {d} pf1 pf2 = let
  sigma x a+x==b = <=-add-get pf1
  sigma y c+y==d = <=-add-get pf2
  eq =
    begin
      (a + c) + (x + y)
    ==[ add-inner-swap a c x y ]
      (a + x) + (c + y)
    ==[ cong (_+ (c + y)) a+x==b ]
      b + (c + y)
    ==[ cong (b +_) c+y==d ]
      b + d
    qed
  in <=-add (x + y) eq

<=-cong-add-r : ∀ {a b} (c : Nat) → a <= b → (a + c) <= (b + c)
<=-cong-add-r c pf = <=-additive pf (<=-refl' {c})

<=-cong-add-l : ∀ {a b} (c : Nat) → a <= b → (c + a) <= (c + b)
<=-cong-add-l c pf = <=-additive (<=-refl' {c}) pf

<=-incr-r : ∀ {a b} → (x : Nat) → a <= b → a <= (b + x)
<=-incr-r {a} {b} x pf = rwt (_<= (b + x)) (add-n-0 a) (<=-additive pf (<=zero x))

<=-incr-l : ∀ {a b} → (x : Nat) → a <= b → a <= (x + b)
<=-incr-l {a} {b} x pf = <=-additive (<=zero x) pf

<=-multiplicative : ∀ {a b c d}
          → a <= b
          → c <= d
          --------------------
          → (a * c) <= (b * d)
<=-multiplicative {a} {b} {c} {d} pf1 pf2 = let
  sigma x a*x==b = <=-add-get pf1
  sigma y c*y==d = <=-add-get pf2
  witness = (a * y) + ((x * c) + (x * y))
  -- Steps needed to prove equality
  step1 = add-assoc (a * c) (a * y) ((x * c) + (x * y)) 
  step2 = cong (_+ ((x * c) + (x * y))) (sym (mul-leftdist a c y)) 
  step3 = cong ((a * (c + y)) +_) (sym (mul-leftdist x c y)) 
  step4 = (sym (mul-rightdist a x (c + y))) 
  step5 = cong (_* (c + y)) a*x==b 
  step6 = cong (b *_) c*y==d 
  eq =
    begin
      (a * c) + ((a * y) + ((x * c) + (x * y)))
    ==[ step1 ]
      ((a * c) + (a * y)) + ((x * c) + (x * y))
    ==[ step2 ]
      (a * (c + y)) + ((x * c) + (x * y))
    ==[ step3 ]
      (a * (c + y)) + (x  * (c + y))
    ==[ step4 ]
      (a + x) * (c + y)
    ==[ step5 ]
      b * (c + y)
    ==[ step6 ]
      b * d
    qed
  in <=-add witness eq

<=-cong-mul-r : ∀ {a b} (c : Nat) → a <= b → (a * c) <= (b * c)
<=-cong-mul-r c pf = <=-multiplicative pf (<=-refl' {c})

<=-cong-mul-l : ∀ {a b} (c : Nat) → a <= b → (c * a) <= (c * b)
<=-cong-mul-l c pf = <=-multiplicative (<=-refl' {c}) pf

<-additive : ∀ {a b c d}
          → a < b
          → c <= d
          --------------------
          → (a + c) < (b + d)
<-additive {a} {b} {c} {d} pf1 pf2 = let
  sigma x 1+a+x==b = <-add-get pf1
  sigma y c+y==d = <=-add-get pf2
  eq =
    begin
      succ ((a + c) + (x + y))
    ==[ cong succ (add-inner-swap a c x y) ]
      succ ((a + x) + (c + y))
    ==[ cong (_+ (c + y)) 1+a+x==b ]
      b + (c + y)
    ==[ cong (b +_) c+y==d ]
      b + d
    qed
  in <-add (x + y) eq

<-additive' : ∀ {a b c d}
          → a <= b
          → c < d
          --------------------
          → (a + c) < (b + d)
<-additive' {a} {b} {c} {d} pf1 pf2 = rwt ((a + c) <_) (add-comm d b) (rwt (_< (d + b)) (add-comm c a) (<-additive pf2 pf1))

-- Strong induction
<=-induction-lemma : {P : Nat -> Set}
                  -> P 0
                  -> ((n : Nat) -> ((m : Nat) -> m <= n -> P m) -> P (succ n))
                  ----------------------------------
                  -> ((n m : Nat) -> m <= n -> P m)
<=-induction-lemma {P} base step 0 m m<=n = rwt P (sym (<=-bottom m<=n)) base
<=-induction-lemma {P} base step (succ n) m m<=1+n =
  case-or (<=-is-<-or-== m<=1+n)
  (λ m<1+n -> <=-induction-lemma base step n m (<-to-<=' m<1+n))
  (λ m==1+n -> rwt P (sym m==1+n) (step n (<=-induction-lemma base step n)))

<=-induction : {P : Nat -> Set}
            -> P 0
            -> ((n : Nat) -> ((m : Nat) -> m <= n -> P m) -> P (succ n))
            ----------------------------------
            -> (n : Nat) -> P n
<=-induction base step n = <=-induction-lemma base step n n <=-refl'

<-induction : {P : Nat -> Set}
            -> ((n : Nat) -> ((m : Nat) -> m < n -> P m) -> P n)
            ----------------------------------
            -> (n : Nat) -> P n
<-induction <-step = let
  base = <-step 0 (λ n n<0 -> absurd (not-n-<-0 n<0))
  step = λ n pf -> <-step (succ n) (λ m m<1+n -> pf m (<-to-<=' m<1+n))
  in <=-induction base step
