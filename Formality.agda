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

-- Several "obvious" postulates that must be proven
postulate
  funext   : {A : Set} → {B : A → Set} → {f g : (x : A) → B x} → (_ : (x : A) → f x == g x) → f == g

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
  var-normal : ∀ a → IsNormal (var a)
  lam-normal : ∀ bod → IsNormal bod -> IsNormal (lam bod)
  app-var-normal : ∀ {fidx arg} → IsNormal arg -> IsNormal (app (var fidx) arg)
  app-app-normal : ∀ {ffun farg arg} → IsNormal (app ffun farg) → IsNormal arg -> IsNormal (app (app ffun farg) arg)

-- This term has redexes
data HasRedex : (t : Term) → Set where
  lam-redex : ∀ bod → HasRedex bod -> HasRedex (lam bod)
  app-redex : ∀ {fun arg} → Or (HasRedex fun) (HasRedex arg) -> HasRedex (app fun arg)
  found-redex : ∀ {fbod arg} → HasRedex (app (lam fbod) arg)

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

-- ::::::::::::::
-- :: Theorems ::
-- ::::::::::::::

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

-- Helper function
subst-fn-elim-aux : (n : Nat) → (arg : Term) → (m : Nat) → subst-fn (at n arg) m == at (succ n) arg m
subst-fn-elim-aux n arg (succ m) = refl
subst-fn-elim-aux n arg zero     = refl

-- Helper function
subst-fn-elim : (n : Nat) → (arg : Term) → subst-fn (at n arg) == at (succ n) arg
subst-fn-elim n arg = funext (subst-fn-elim-aux n arg)

-- Converts the size of a substitution into a mathematical expression
-- That is, size(t[x <- a]) == size(t) + uses(x, t) * size(a)
size-after-subst : ∀ n bod arg → size (subst (at n arg) bod) == (size bod + (uses bod n * size arg))
size-after-subst n (var bidx) arg with ==dec bidx n
size-after-subst n (var bidx) arg | (or0 e) = rwt (λ x → size (at n arg bidx) == x) (sym (add-n-0 (size arg))) (subst-hit-size n bidx arg e)
size-after-subst n (var bidx) arg | (or1 e) = subst-miss-size n bidx arg e
size-after-subst n (lam bbod) arg =
  let a = size-after-subst (succ n) bbod arg
      b = subst-fn-elim n arg  
      c = rwt (λ x → size (subst x bbod) == (size bbod + (uses bbod (succ n) * size arg))) (sym b) a
  in  cong succ c
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

postulate
  reduce-uses-lemma : (n : Nat) → (arg bod : Term) → IsAffine (lam bod) → (uses (subst (at 0 arg) bod) n) <= (uses bod (succ n) + uses arg n)
  reduce-affine : (t : Term) → IsAffine t → IsAffine (reduce t)

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
  <=[ <=-refl' ]
    uses (app (reduce (app ffun farg)) (reduce arg)) n
  <=[ <=-refl' ]
    uses (reduce (app ffun farg)) n + uses (reduce arg) n
  <=[ <=-additive pf1 pf2 ]
    uses (app ffun farg) n + uses arg n
  <=[ <=-refl' ]
    uses (app (app ffun farg) arg) n
  qed<=
reduce-uses n (app (lam bod) arg) (app-affine (lam-affine eq bod-af) arg-af) =
  let pf1 = reduce-uses n (lam bod) (lam-affine eq bod-af)
      pf2 = reduce-uses n arg arg-af
  in
  begin<=
    uses (reduce (app (lam bod) arg)) n
  <=[ <=-refl' ]
    uses (subst (at zero (reduce arg)) (reduce bod)) n
  <=[ reduce-uses-lemma n (reduce arg) (reduce bod) (reduce-affine (lam bod) (lam-affine eq bod-af)) ]
     uses (reduce bod) (succ n) + uses (reduce arg) n
  <=[ <=-additive pf1 pf2 ]
    uses bod (succ n) + uses arg n
  <=[ <=-refl' ]
    uses (app (lam bod) arg) n
  qed<=

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
  <=[ <=-refl' ]
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
  <=[ <=-refl' ]
    size (app (lam fbod) arg)
  qed<=

-- Reducing an affine term with redexes reduces its size
reduce< : (t : Term) → IsAffine t → HasRedex t → size (reduce t) < size t
reduce< (var idx) _ ()
reduce< (lam bod) (lam-affine _ af) (lam-redex _ hr) = <succ (reduce< bod af hr)
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
  <='[ <=-refl' ]
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
  <=[ <=-refl' ]
    size (app (lam fbod) arg)
  qed<

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
