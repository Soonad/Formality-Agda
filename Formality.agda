-- :::::::::::::
-- :: Prelude ::
-- :::::::::::::

module Formality where
open import Logic
open import Nat
open import Equality
open import EquationalReasoning

-- This enables the "case-of idiom", which isn't built-in
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

-- This enables the "inspect idiom", which isn't built-in
module _ {A : Set} {B : A → Set} where
  data Graph (f : ∀ x → B x) (x : A) (y : B x) : Set where
    its : f x == y → Graph f x y
  inspect : (f : ∀ x → B x) (x : A) → Graph f x (f x)
  inspect _ _ = its refl

-- ::::::::::::::
-- :: Language ::
-- ::::::::::::::

-- A λ-calculus term. We're keeping types as simple as possible, so we don't
-- keep a Fin index tracking free vars, nor contexts in any form
data Term : Set where
  var : Nat -> Term
  lam : Term -> Term
  app : Term -> Term -> Term

-- Adjusts a renaming function
shift-fn : (Nat -> Nat) -> Nat -> Nat
shift-fn fn zero     = zero
shift-fn fn (succ i) = succ (fn i)

shift-fn-many : Nat -> (Nat -> Nat) -> Nat -> Nat
shift-fn-many n fn = pow shift-fn n fn

-- Renames all free variables with a renaming function, `fn`
shift : (Nat -> Nat) -> Term -> Term
shift fn (var i)       = var (fn i)
shift fn (lam bod)     = lam (shift (shift-fn fn) bod)
shift fn (app fun arg) = app (shift fn fun) (shift fn arg)

-- Adjusts a substitution map
subst-fn : (Nat → Term) → Nat → Term
subst-fn fn zero     = var zero
subst-fn fn (succ i) = shift succ (fn i)

-- Substitutes all free vars on term with a substitution map, `fn`
subst : (Nat -> Term) -> Term -> Term
subst fn (var i)       = fn i
subst fn (lam bod)     = lam (subst (subst-fn fn) bod) 
subst fn (app fun arg) = app (subst fn fun) (subst fn arg)

-- Creates a substitution map that replaces only one variable
at : Nat → Term → Nat → Term
at zero     term zero     = term
at zero     term (succ i) = var i
at (succ n) term = subst-fn (at n term)

-- Performs a global reduction of all current redexes
reduce : Term -> Term
reduce (var i)             = var i
reduce (lam bod)           = lam (reduce bod)
reduce (app (var idx) arg)       = app (var idx) (reduce arg)
reduce (app (lam bod) arg) = subst (at zero (reduce arg)) (reduce bod)
reduce (app (app ffun farg) arg)       = app (reduce (app ffun farg)) (reduce arg)

-- Computes how many times a free variable is used
uses : Term -> Nat -> Nat
uses (var i)       n with ==dec i n
uses (var i)       n | or0 _  = 1
uses (var i)       n | or1 _ = 0
uses (lam bod)     n = uses bod (succ n)
uses (app fun arg) n = uses fun n + uses arg n

uses-step : {i n : Nat} -> uses (var (succ i)) (succ n) == uses (var i) n
uses-step {i} {n} with ==dec i n
uses-step {i} {n} | or0 _ = refl
uses-step {i} {n} | or1 _ = refl

uses-n-step : {i n : Nat} -> (p : Nat) -> uses (var (p + i)) (p + n) == uses (var i) n
uses-n-step 0 = refl
uses-n-step (succ p) = trans uses-step (uses-n-step p)

-- Computes the size of a term
size : Term -> Nat
size (var i)       = 0
size (lam bod)     = succ (size bod)
size (app fun arg) = succ (size fun + size arg)

-- This term is affine
data IsAffine : (t : Term) → Set where
  var-affine : ∀ {a} → IsAffine (var a)
  lam-affine : ∀ {bod} → (uses bod 0 <= 1) → IsAffine bod -> IsAffine (lam bod)
  app-affine : ∀ {fun arg} → IsAffine fun → IsAffine arg -> IsAffine (app fun arg)

-- This term is on normal form
data IsNormal : (t : Term) → Set where
  var-normal : ∀ {a} → IsNormal (var a)
  lam-normal : ∀ {bod} → IsNormal bod -> IsNormal (lam bod)
  app-var-normal : ∀ {fidx arg} → IsNormal arg -> IsNormal (app (var fidx) arg)
  app-app-normal : ∀ {ffun farg arg} → IsNormal (app ffun farg) → IsNormal arg -> IsNormal (app (app ffun farg) arg)

-- This term has redexes
data HasRedex : (t : Term) → Set where
  lam-redex : ∀ {bod} → HasRedex bod -> HasRedex (lam bod)
  app-redex : ∀ {fun arg} → Or (HasRedex fun) (HasRedex arg) -> HasRedex (app fun arg)
  found-redex : ∀ {fbod arg} → HasRedex (app (lam fbod) arg)

-- A normal term has no redexes
normal-has-noredex : (t : Term) → IsNormal t → Not (HasRedex t)
normal-has-noredex (lam bod) (lam-normal bod-isnormal) (lam-redex bod-hasredex) = normal-has-noredex bod bod-isnormal bod-hasredex
normal-has-noredex (app (var idx) arg) (app-var-normal arg-isnormal) (app-redex (or1 arg-hasredex)) = normal-has-noredex arg arg-isnormal arg-hasredex
normal-has-noredex (app (app ffun farg) arg) (app-app-normal fun-isnormal _) (app-redex (or0 fun-hasredex)) = normal-has-noredex (app ffun farg) fun-isnormal fun-hasredex 
normal-has-noredex (app (app ffun farg) arg) (app-app-normal _ arg-isnormal) (app-redex (or1 arg-hasredex)) = normal-has-noredex arg arg-isnormal arg-hasredex

-- A term that has no redexes is normal
noredex-is-normal : (t : Term) → Not (HasRedex t) → IsNormal t
noredex-is-normal (var idx) noredex = var-normal
noredex-is-normal (lam bod) noredex = lam-normal (noredex-is-normal bod (λ x → noredex (lam-redex x)))
noredex-is-normal (app (var idx) arg) noredex = app-var-normal (noredex-is-normal arg (λ x → noredex (app-redex (or1 x))))
noredex-is-normal (app (app ffun farg) arg) noredex = app-app-normal (noredex-is-normal (app ffun farg) (λ x → noredex (app-redex (or0 x)))) (noredex-is-normal arg (λ x → noredex (app-redex (or1 x))))
noredex-is-normal (app (lam bod) arg) noredex = absurd (noredex found-redex)

-- Computes the number of redexes in a term
redexes : (t : Term) → Nat
redexes (var idx)                 = 0
redexes (lam bod)                 = redexes bod
redexes (app (var fidx)      arg) = redexes arg
redexes (app (lam fbod)      arg) = 1 + (redexes fbod + redexes arg)
redexes (app (app ffun farg) arg) = redexes (app ffun farg) + redexes arg

-- Directed one step reduction relation, `a ~> b` means term `a` reduces to `b` in one step
data _~>_ : Term → Term → Set where
  ~beta : ∀ {t u} → app (lam t) u ~> subst (at 0 u) t
  ~app0 : ∀ {f0 f1 a} → f0 ~> f1 → app f0 a ~> app f1 a
  ~app1 : ∀ {f a0 a1} → a0 ~> a1 → app f a0 ~> app f a1
  ~lam0 : ∀ {b0 b1} → b0 ~> b1 → lam b0 ~> lam b1

-- :::::::::::::::::::::::::
-- :: Theorems and lemmas ::
-- :::::::::::::::::::::::::

shift-0-aux1 : ∀ idx m → shift-fn-many m (0 +_) idx == idx
shift-0-aux1 idx 0 = refl
shift-0-aux1 0 (succ m) = refl
shift-0-aux1 (succ idx) (succ m) = cong succ (shift-0-aux1 idx m)

shift-0-aux2 : ∀ term m → shift (shift-fn-many m (0 +_)) term == term
shift-0-aux2 (var idx) m = cong var (shift-0-aux1 idx m)
shift-0-aux2 (lam bod) m = cong lam (shift-0-aux2 bod (succ m))
shift-0-aux2 (app fun arg) m = trans (cong (λ x → app x (shift (shift-fn-many m (0 +_)) arg)) (shift-0-aux2 fun m)) (cong (λ x → app fun x) (shift-0-aux2 arg m))

shift-0 : ∀ term → shift (0 +_) term == term
shift-0 term = shift-0-aux2 term 0

shift-succ-aux1 : ∀ a idx m → shift-fn-many m succ (shift-fn-many m (a +_) idx) == shift-fn-many m (succ a +_) idx
shift-succ-aux1 0 idx m = cong (shift-fn-many m succ) (shift-0-aux1 idx m)
shift-succ-aux1 (succ a) idx 0 = refl
shift-succ-aux1 (succ a) 0 (succ m) = refl
shift-succ-aux1 (succ a) (succ idx) (succ m) = cong succ (shift-succ-aux1 (succ a) idx m)

shift-succ-aux2 : ∀ a term m → shift (shift-fn-many m succ) (shift (shift-fn-many m (a +_)) term) == shift (shift-fn-many m (succ a +_)) term
shift-succ-aux2 0 term m = cong (λ x → shift (shift-fn-many m succ) x) (shift-0-aux2 term m)
shift-succ-aux2 (succ a) (var idx) m = cong var (shift-succ-aux1 (succ a) idx m)
shift-succ-aux2 (succ a) (lam bod) m = cong lam (shift-succ-aux2 (succ a) bod (succ m))
shift-succ-aux2 (succ a) (app fun arg) m =
  let term1 = shift (shift-fn-many m succ) (shift (shift-fn-many m (succ a +_)) arg)
      term2 = shift (shift-fn-many m (succ (succ a) +_)) fun
  in trans (cong (λ x → app x term1) (shift-succ-aux2 (succ a) fun m)) (cong (λ x → app term2 x) (shift-succ-aux2 (succ a) arg m))

shift-succ : ∀ a term → shift succ (shift (a +_) term) == shift (succ a +_) term
shift-succ a term = shift-succ-aux2 a term 0

shift-add : ∀ a b term → shift (a +_) (shift (b +_) term) == shift ((a + b) +_) term
shift-add 0 b term = shift-0 (shift (b +_) term)
shift-add (succ a) b term =
  begin
    shift (succ a +_) (shift (b +_) term)
  ==[ sym (shift-succ a (shift (b +_) term)) ]
    shift succ (shift (a +_) (shift (b +_) term))
  ==[ cong (shift succ) (shift-add a b term) ]
    shift succ (shift ((a + b) +_) term)
  ==[ shift-succ (a + b) term ]
    shift ((succ a + b) +_) term
  qed

at-lemma1 : ∀ m idx arg → m == idx → at m arg idx == shift (m +_) arg
at-lemma1 0 0 arg eq = sym (shift-0 arg)
at-lemma1 (succ m) (succ idx) arg eq = trans (cong (λ x → shift succ x) (at-lemma1 m idx arg (succ-inj eq))) (shift-succ m arg)

at-lemma2 : ∀ m idx arg → m < (succ idx) → at m arg (succ idx) == var idx
at-lemma2 0 idx arg _ = refl
at-lemma2 (succ m) (succ idx) arg (<succ idx<m) = cong (λ x → shift succ x) (at-lemma2 m idx arg idx<m)

at-lemma3 : ∀ m idx arg → idx < m → at m arg idx == var idx
at-lemma3 (succ m) 0 arg _ = refl
at-lemma3 (succ m) (succ idx) arg (<succ idx<m) = cong (λ x → shift succ x) (at-lemma3 m idx arg idx<m)

shift-fn-lemma1 : (n m p : Nat) → m <= n → shift-fn-many m (p +_) n == (p + n)
shift-fn-lemma1 n 0 p _ = refl
shift-fn-lemma1 (succ n) (succ m) 0 (<=succ lte) = cong succ (shift-fn-lemma1 n m 0 lte)
shift-fn-lemma1 (succ n) (succ m) (succ p) (<=succ lte) =
  begin
    succ (shift-fn-many m (succ p +_) n)
  ==[ cong succ (shift-fn-lemma1 n m (succ p) lte) ]
    succ (succ (p + n))
  ==[ sym (add-n-succ (succ p) n) ]
    (succ p + succ n)
  qed

shift-fn-lemma2 : (fn : Nat → Nat) → (n m : Nat) → (succ n) <= m → shift-fn-many m fn n == n
shift-fn-lemma2 fn 0 (succ m) (<=succ lte) = refl
shift-fn-lemma2 fn (succ n) (succ m) (<=succ lte) = cong succ (shift-fn-lemma2 fn n m lte)

-- Shifting a term doesn't affect its size
shift-preserves-size : ∀ fn term → size (shift fn term) == size term
shift-preserves-size fn (var idx)     = refl
shift-preserves-size fn (lam bod)     = cong succ (shift-preserves-size (shift-fn fn) bod)
shift-preserves-size fn (app fun arg) =
  let a = shift-preserves-size fn fun
      b = shift-preserves-size fn arg
      c = refl {x = size fun + size arg}
      d = rwt (λ x → (x + (size arg))          == (size fun + size arg)) (sym a) c
      e = rwt (λ x → (size (shift fn fun) + x) == (size fun + size arg)) (sym b) d
  in  cong succ e

-- Helper function 
subst-miss-size : (n : Nat) → (bidx : Nat) → (arg : Term) → Not(bidx == n) → size (at n arg bidx) == 0
subst-miss-size (succ n) (succ bidx) arg s = trans (shift-preserves-size succ (at n arg bidx)) (subst-miss-size n bidx arg (modus-tollens (cong succ) s))
subst-miss-size (succ n) zero        arg s = refl
subst-miss-size zero     (succ bidx) arg s = refl
subst-miss-size zero     zero        arg s = absurd (s refl)

-- Helper function 
subst-hit-size : (n : Nat) → (bidx : Nat) → (arg : Term) → bidx == n → size (at n arg bidx) == size arg
subst-hit-size (succ n) (succ bidx) arg s = trans (shift-preserves-size succ (at n arg bidx)) (subst-hit-size n bidx arg (succ-inj s))
subst-hit-size (succ n) zero        arg ()
subst-hit-size zero     (succ bidx) arg ()
subst-hit-size zero     zero        arg s = refl

-- Converts the size of a substitution into a mathematical expression
-- That is, size(t[x <- a]) == size(t) + uses(x, t) * size(a)
size-after-subst : ∀ n bod arg → size (subst (at n arg) bod) == (size bod + (uses bod n * size arg))
size-after-subst n (var bidx) arg with ==dec bidx n
size-after-subst n (var bidx) arg | (or0 e) = rwt (λ x → size (at n arg bidx) == x) (sym (add-n-0 (size arg))) (subst-hit-size n bidx arg e)
size-after-subst n (var bidx) arg | (or1 e) = subst-miss-size n bidx arg e
size-after-subst n (lam bbod) arg =
  let a = size-after-subst (succ n) bbod arg
      b = rwt (λ x → size (subst x bbod) == (size bbod + (uses bbod (succ n) * size arg))) refl a
  in  cong succ b
size-after-subst n (app bfun barg) arg =
  let a = size-after-subst n bfun arg
      b = size-after-subst n barg arg
      c = refl {x = (size (subst (at n arg) bfun) + size (subst (at n arg) barg))}
      d = rwt (λ x → (x + size (subst (at n arg) barg)) == (size (subst (at n arg) bfun) + size (subst (at n arg) barg))) a c
      e = rwt (λ x → ((size bfun + (uses bfun n * size arg)) + x) == (size (subst (at n arg) bfun) + size (subst (at n arg) barg))) b d
      f = add-inner-swap (size bfun) (uses bfun n * size arg) (size barg) (uses barg n * size arg)
      g = sym (rwt (λ x → x == (size (subst (at n arg) bfun) + size (subst (at n arg) barg))) f e)
      h = sym (mul-rightdist (uses bfun n) (uses barg n) (size arg))
      i = rwt (λ x → (size (subst (at n arg) bfun) + size (subst (at n arg) barg)) == ((size bfun + size barg) + x)) h g
  in  cong succ i

uses-0-lemma : (idx n : Nat) -> (succ idx) <= n -> uses (var idx) n == 0
uses-0-lemma idx (succ n) leq with ==dec idx (succ n)
uses-0-lemma idx (succ n) leq | or1 _ = refl
uses-0-lemma idx (succ n) (<=succ leq) | or0 eq = absurd (rwt (λ x → Not (x <= n)) (sym eq) (<-to-not->= (n-<-succ {n})) leq)

var-uses<=1 : {idx n : Nat} -> uses (var idx) n <= 1
var-uses<=1 {0} {0} = <=-refl'
var-uses<=1 {0} {succ n} = <=zero 1
var-uses<=1 {succ idx} {0} = <=zero 1
var-uses<=1 {succ idx} {succ n} = <=-trans (<=-refl uses-step) var-uses<=1

uses-add-lemma : (term : Term) → (n m p : Nat) → m <= n → uses (shift (shift-fn-many m (p +_)) term) (p + n) == uses term n
uses-add-lemma (var idx) n 0 0 _ = refl
uses-add-lemma (var idx) n 0 (succ p) _ =
    uses (var (succ p + idx)) (succ p + n) 
  ==[]
    uses (var (succ p + idx)) (succ p + n) 
  ==[ uses-step ]
    uses (var (p + idx)) (p + n)
  ==[ uses-add-lemma (var idx) n 0 p (<=zero n) ]
    uses (var idx) n
  qed
uses-add-lemma (var idx) (succ n) (succ m) p (<=succ m<=n) with <=-total (succ m) idx
uses-add-lemma (var idx) (succ n) (succ m) p (<=succ m<=n) | or0 1+m<=idx  =
  begin
    uses (shift (shift-fn-many (succ m) (p +_)) (var idx)) (p + succ n)
  ==[]
    uses (var (shift-fn-many (succ m) (p +_) idx)) (p + succ n)
  ==[ cong (λ x → uses (var x) (p + succ n)) (shift-fn-lemma1 idx (succ m) p 1+m<=idx) ]
    uses (var (p + idx)) (p + succ n)
  ==[ uses-n-step p ]
    uses (var idx) (succ n)
  qed
uses-add-lemma (var idx) (succ n) (succ m) p (<=succ m<=n) | or1 (<=succ idx<=m) =
  let idx<=n = <=-trans idx<=m m<=n
      q = <=succ idx<=n
      q' = <=-incr-l p q
  in
    begin
    uses (var (shift-fn-many (succ m) (_+_ p) idx)) (p + succ n)
  ==[ cong (λ x → uses (var x) (p + succ n)) (shift-fn-lemma2 (p +_) idx (succ m) (<=succ idx<=m)) ]
    uses (var idx) (p + succ n)
  ==[ uses-0-lemma idx (p + succ n) q' ]
    0
  ==[ sym (uses-0-lemma idx (succ n) q) ]
    uses (var idx) (succ n)
  qed
uses-add-lemma (app fun arg) n m p leq =
  begin
    uses (shift (shift-fn-many m (p +_)) (app fun arg)) (p + n)
  ==[]
    uses (shift (shift-fn-many m (p +_)) fun) (p + n) + uses (shift (shift-fn-many m (p +_)) arg) (p + n)
  ==[ cong (_+ uses (shift (shift-fn-many m (p +_)) arg) (p + n)) (uses-add-lemma fun n m p leq)  ]
    uses fun n + uses (shift (shift-fn-many m (p +_)) arg) (p + n)
  ==[ cong (uses fun n +_) (uses-add-lemma arg n m p leq)  ]
    uses (app fun arg) n
    qed
uses-add-lemma (lam bod) n m p leq =
  begin
    uses (shift (shift-fn-many m (p +_)) (lam bod)) (p + n)
  ==[]
    uses (shift (shift-fn-many (succ m) (p +_)) bod) (succ p + n)
  ==[ cong (λ x → uses (shift (shift-fn-many (succ m) (p +_)) bod) x) (sym (add-n-succ p n)) ]
    uses (shift (shift-fn-many (succ m) (p +_)) bod) (p + succ n)
  ==[ uses-add-lemma bod (succ n) (succ m) p (<=succ leq) ]
    uses bod (succ n)
  ==[]
    uses (lam bod) n
  qed

uses-add : (term : Term) → (n p : Nat) → uses (shift (p +_) term) (p + n) == uses term n
uses-add term n p = uses-add-lemma term n 0 p (<=zero n)

uses-succ : (term : Term) → (n : Nat) → uses (shift succ term) (succ n) == uses term n
uses-succ term n = uses-add-lemma term n 0 1 (<=zero n)

uses-subst-0 : (n m : Nat) → (arg bod : Term) → (uses bod m) == 0 → uses (subst (at m arg) bod) (m + n) == uses bod (succ (m + n))
uses-subst-0 n 0 arg (var (succ idx)) pf = sym (uses-succ (var idx) n)
uses-subst-0 n (succ m) arg (var 0) pf = refl
uses-subst-0 n (succ m) arg (var (succ idx)) pf =
    uses (shift succ (at m arg idx)) (succ m + n)
  ==[ uses-succ (at m arg idx) (m + n) ]
    uses (at m arg idx) (m + n)
  ==[ uses-subst-0 n m arg (var idx) (trans (sym uses-step) pf) ]
    uses (var idx) (succ m + n)
  ==[ sym (uses-succ (var idx) (succ m + n)) ]
    uses (var (succ idx)) (succ (succ m + n))
  qed
uses-subst-0 n m arg (lam bod) pf = uses-subst-0 n (succ m) arg bod pf
uses-subst-0 n m arg (app fun arg') pf =
  let and eq1 eq2 = add-no-inverse (uses fun m) (uses arg' m) pf
  in
  begin
  begin
    uses (subst (at m arg) fun) (m + n) + uses (subst (at m arg) arg') (m + n)
  ==[ cong (_+ uses (subst (at m arg) arg') (m + n)) (uses-subst-0 n m arg fun eq1) ]
    uses fun (succ m + n) + uses (subst (at m arg) arg') (m + n)
  ==[ cong (uses fun (succ m + n) +_) (uses-subst-0 n m arg arg' eq2) ]
    uses fun (succ m + n) + uses arg' (succ m + n)
  qed

uses-subst-1 : (n m : Nat) → (arg bod : Term) → (uses bod m) == 1 → (uses (subst (at m arg) bod) (m + n)) == (uses bod (succ (m + n)) + uses arg n)
uses-subst-1 n 0 arg (var 0) pf = refl
uses-subst-1 n (succ m) arg (var (succ idx)) pf =
  begin
    uses (shift succ (at m arg idx)) (succ m + n)
  ==[ uses-succ (at m arg idx) (m + n) ]
    uses (at m arg idx) (m + n)
  ==[ uses-subst-1 n m arg (var idx) (trans (sym uses-step) pf) ]
    uses (var idx) (succ m + n) + uses arg n
  ==[ cong (_+ uses arg n) (sym (uses-succ (var idx) (succ m + n))) ]
    uses (var (succ idx)) (succ (succ m + n)) + uses arg n
  qed
uses-subst-1 n m arg (lam bod) pf = uses-subst-1 n (succ m) arg bod pf
uses-subst-1 n m arg (app fun arg') pf =
  let case0 x =
        let and eq1 eq2 = x in
        begin
          uses (subst (at m arg) fun) (m + n) + uses (subst (at m arg) arg') (m + n)
        ==[ cong (_+ uses (subst (at m arg) arg') (m + n)) (uses-subst-0 n m arg fun eq1)]
          uses fun (succ m + n) + uses (subst (at m arg) arg') (m + n)
        ==[ cong (uses fun (succ m + n) +_) (uses-subst-1 n m arg arg' eq2) ]
          uses fun (succ m + n) + (uses arg' (succ m + n) + uses arg n)
        ==[ add-assoc (uses fun (succ m + n)) (uses arg' (succ m + n)) (uses arg n) ]
          (uses fun (succ m + n) + uses arg' (succ m + n)) + uses arg n
        qed
      case1 x =
        let and eq1 eq2 = x in
        begin
          uses (subst (at m arg) fun) (m + n) + uses (subst (at m arg) arg') (m + n)
        ==[ cong (uses (subst (at m arg) fun) (m + n) +_) (uses-subst-0 n m arg arg' eq1)]
          uses (subst (at m arg) fun) (m + n) + uses arg' (succ m + n)
        ==[ cong (_+ uses arg' (succ m + n)) (uses-subst-1 n m arg fun eq2) ]
          (uses fun (succ m + n) + uses arg n) + uses arg' (succ m + n)
        ==[ add-right-swap (uses fun (succ m + n)) (uses arg n) (uses arg' (succ m + n)) ]
          (uses fun (succ m + n) + uses arg' (succ m + n)) + uses arg n
        qed
  in case-or (fact (uses fun m) (uses arg' m) pf) case0 case1

reduce-uses-lemma : (n : Nat) → (arg bod : Term) → uses bod 0 <= 1 → (uses (subst (at 0 arg) bod) n) <= (uses bod (succ n) + uses arg n)
reduce-uses-lemma n arg bod pf with uses bod 0             | inspect (uses bod) 0
reduce-uses-lemma n arg bod _            | 0               | its e = <=-incr-r (uses arg n) (<=-refl (uses-subst-0 n 0 arg bod e))
reduce-uses-lemma n arg bod _            | 1               | its e = <=-refl (uses-subst-1 n 0 arg bod e)
reduce-uses-lemma n arg bod (<=succ leq) | (succ (succ m)) | its e = absurd (succ-not-<=-0 leq)

reduce-uses : (n : Nat) → (t : Term) → IsAffine t → uses (reduce t) n <= uses t n
reduce-uses n (var idx) _ = <=-refl'
reduce-uses n (lam bod) (lam-affine _ af) = reduce-uses (succ n) bod af
reduce-uses n (app (var idx) arg) (app-affine _ af) = <=-cong-add-l (uses (var idx) n) (reduce-uses n arg af)
reduce-uses n (app (app ffun farg) arg) (app-affine (app-affine ffun-af farg-af) arg-af) =
  let pf1 = reduce-uses n (app ffun farg) (app-affine ffun-af farg-af)
      pf2 = reduce-uses n arg arg-af
  in
  begin<=
    uses (reduce (app (app ffun farg) arg)) n
  <=[]
    uses (app (reduce (app ffun farg)) (reduce arg)) n
  <=[]
    uses (reduce (app ffun farg)) n + uses (reduce arg) n
  <=[ <=-additive pf1 pf2 ]
    uses (app ffun farg) n + uses arg n
  <=[]
    uses (app (app ffun farg) arg) n
  qed<=
reduce-uses n (app (lam bod) arg) (app-affine (lam-affine eq bod-af) arg-af) =
  let pf1 = reduce-uses n (lam bod) (lam-affine eq bod-af)
      pf2 = reduce-uses n arg arg-af
  in
  begin<=
    uses (reduce (app (lam bod) arg)) n
  <=[]
    uses (subst (at zero (reduce arg)) (reduce bod)) n
  <=[ reduce-uses-lemma n (reduce arg) (reduce bod) (<=-trans (reduce-uses 0 bod bod-af) eq) ]
     uses (reduce bod) (succ n) + uses (reduce arg) n
  <=[ <=-additive pf1 pf2 ]
    uses bod (succ n) + uses arg n
  <=[]
    uses (app (lam bod) arg) n
  qed<=

postulate
  reduce-affine-lemma : (arg bod : Term) → IsAffine arg → IsAffine bod → (m : Nat) → (uses bod m) <= 1 → IsAffine (subst (at m arg) bod)

reduce-affine : (t : Term) → IsAffine t → IsAffine (reduce t)
reduce-affine (var idx) af = var-affine
reduce-affine (lam bod) (lam-affine leq bod-af) = lam-affine (<=-trans (reduce-uses 0 bod bod-af) leq) (reduce-affine bod bod-af)
reduce-affine (app (var idx) arg) (app-affine _ arg-af) = app-affine var-affine (reduce-affine arg arg-af)
reduce-affine (app (app ffun farg) arg) (app-affine fun-af arg-af) = app-affine (reduce-affine (app ffun farg) fun-af) (reduce-affine arg arg-af)
reduce-affine (app (lam bod) arg) (app-affine (lam-affine leq bod-af) arg-af) =
  let red-arg-af = (reduce-affine arg arg-af)
      red-bod-af = (reduce-affine bod bod-af)
  in reduce-affine-lemma (reduce arg) (reduce bod) red-arg-af red-bod-af 0 (<=-trans (reduce-uses 0 bod bod-af) leq)

-- Reducing an affine term either reduces its size or keeps it the same
reduce<= : (t : Term) → IsAffine t → size (reduce t) <= size t
reduce<= (var idx) _ = <=zero zero
reduce<= (lam bod) (lam-affine _ af) = <=succ (reduce<= bod af)
reduce<= (app (var fidx) arg) (app-affine _ af) = <=succ (reduce<= arg af) 
reduce<= (app (app ffun farg) arg) (app-affine af-fun af-arg) = <=succ (<=-additive (reduce<= (app ffun farg) af-fun) (reduce<= arg af-arg))
reduce<= (app (lam fbod) arg) (app-affine (lam-affine leq af-bod) af-arg) =
  let step1 = <=-refl (size-after-subst 0 (reduce fbod) (reduce arg))
      step2 = <=-cong-add-r (uses (reduce fbod) 0 * size (reduce arg)) (reduce<= fbod af-bod)
      step3 = <=-cong-add-l (size fbod) (<=-cong-mul-l (uses (reduce fbod) 0) (reduce<= arg af-arg))
      step4 = <=-cong-add-l (size fbod) (<=-cong-mul-r (size arg) (reduce-uses 0 fbod af-bod))
      step5 = <=-cong-add-l (size fbod) (<=-cong-mul-r (size arg) leq)
      step6 = <=-cong-add-l (size fbod) (<=-refl (add-n-0 (size arg)))
      step7 = <=-incr-l 2 <=-refl'
  in
  begin<= 
    size (reduce (app (lam fbod) arg))
  <=[]
    size (subst (at 0 (reduce arg)) (reduce fbod))
  <=[ step1 ]
    size (reduce fbod) + (uses (reduce fbod) 0 * size (reduce arg))
  <=[ step2 ]
    size fbod + (uses (reduce fbod) 0 * size (reduce arg))
  <=[ step3 ]
    size fbod + (uses (reduce fbod) 0 * size arg)
  <=[ step4 ]
    size fbod + (uses fbod 0 * size arg)
  <=[ step5 ]
    size fbod + (1 * size arg)
  <=[ step6 ]
    size fbod + size arg
  <=[ step7 ]
    succ (succ (size fbod + size arg))
  <=[]
    size (app (lam fbod) arg)
  qed<=

-- Reducing an affine term with redexes reduces its size
reduce< : (t : Term) → IsAffine t → HasRedex t → size (reduce t) < size t
reduce< (var idx) _ ()
reduce< (lam bod) (lam-affine _ af) (lam-redex hr) = <succ (reduce< bod af hr)
reduce< (app (var fidx) arg) (app-affine _ af) (app-redex (or1 o1)) = <succ (reduce< arg af o1)
reduce< (app (app ffun farg) arg) (app-affine leq af) (app-redex (or0 o0)) =
  <succ (<-additive (reduce< (app ffun farg) leq o0) (reduce<= arg af))
reduce< (app (app ffun farg) arg) (app-affine leq af) (app-redex (or1 o1)) =
  let a = reduce<= (app ffun farg) leq
      b = reduce< arg af o1
      c = <-additive' a b
  in  <succ c
reduce< (app (lam fbod) arg) (app-affine (lam-affine leq af-bod) af-arg) foundredex =
  let step1 = <=-refl (size-after-subst 0 (reduce fbod) (reduce arg))
      step2 = <=-cong-add-r (uses (reduce fbod) 0 * size (reduce arg)) (reduce<= fbod af-bod)
      step3 = <=-cong-add-l (size fbod) (<=-cong-mul-l (uses (reduce fbod) 0) (reduce<= arg af-arg))
      step4 = <=-cong-add-l (size fbod) (<=-cong-mul-r (size arg) (reduce-uses 0 fbod af-bod))
      step5 = <=-cong-add-l (size fbod) (<=-cong-mul-r (size arg) leq)
      step6 = <=-cong-add-l (size fbod) (<=-refl (add-n-0 (size arg)))
      step7 = <=-incr-l 1 <=-refl'
  in
  begin< 
    size (reduce (app (lam fbod) arg))
  <='[]
    size (subst (at 0 (reduce arg)) (reduce fbod))
  <='[ step1 ]
    size (reduce fbod) + (uses (reduce fbod) 0 * size (reduce arg))
  <='[ step2 ]
    size fbod + (uses (reduce fbod) 0 * size (reduce arg))
  <='[ step3 ]
    size fbod + (uses (reduce fbod) 0 * size arg)
  <='[ step4 ]
    size fbod + (uses fbod 0 * size arg)
  <='[ step5 ]
    size fbod + (1 * size arg)
  <='[ step6 ]
    size fbod + size arg
  <[ n-<-succ  ]
    succ (size fbod + size arg)
  <=[ step7  ]
    succ (succ (size fbod + size arg))
  <=[]
    size (app (lam fbod) arg)
  qed<

normalize-aux : (t : Term) → IsAffine t → Nat → Term
normalize-aux t af n = t

-- :::::::::::
-- :: Tests ::
-- :::::::::::

n2 : Term
n2 = lam (lam (app (var 1) (app (var 1) (var 0))))

n3 : Term
n3 = lam (lam (app (var 1) (app (var 1) (app (var 1) (var 0)))))

n4 : Term
n4 = lam (lam (app (var 1) (app (var 1) (app (var 1) (app (var 1) (var 0))))))

foo : Term
foo = lam (lam (app (var 0) (app (var 1) (app (var 1) (app (var 2) (app (var 2) (app (var 3) (app (var 3) (var 3)))))))))

test-0 : reduce (reduce (reduce (app n2 n2))) == n4
test-0 = refl

main : Nat
main = 7 * 4
