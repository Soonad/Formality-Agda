-- :::::::::::::
-- :: Prelude ::
-- :::::::::::::

module Formality where
open import Logic
open import Nat
open import Equality

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
  <dist    : ∀ {a b c d} → a < b → c < d → (a + c) < (b + d)
  <=dist   : ∀ {a b c d} → a <= b → c <= d → (a + c) <= (b + d)
  <<=dist  : ∀ {a b c d} → a < b → c <= d → (a + c) < (b + d)
  <=<dist  : ∀ {a b c d} → a <= b → c < d → (a + c) < (b + d)
  <=fct0   : ∀ {a b c0 c1 d} → c0 <= c1 → a <= (b + (c0 * d)) → a <= (b + (c1 * d))
  <=fct1   : ∀ {a b0 b1 c} → b0 <= b1 → a <= (b0 + c) → a <= (b1 + c)
  <=fct2   : ∀ {a b c0 c1} → c0 <= c1 → a <= (b + c0) → a <= (b + c1)

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
at (succ n) term zero     = var zero
at (succ n) term (succ i) = shift succ (at n term i)

-- Performs a global reduction of all current redexes
reduce : Term -> Term
reduce (var i)             = var i
reduce (lam bod)           = lam (reduce bod)
reduce (app (lam bod) arg) = subst (at zero (reduce arg)) (reduce bod)
reduce (app fun arg)       = app (reduce fun) (reduce arg)

-- Computes how many times a free variable is used
uses : Term -> Nat -> Nat
uses (var i)       n with same i n
uses (var i)       n | true  = 1
uses (var i)       n | false = 0
uses (lam bod)     n = uses bod (succ n)
uses (app fun arg) n = uses fun n + uses arg n

-- Computes the size of a term
size : Term -> Nat
size (var i)       = 0
size (lam bod)     = succ (size bod)
size (app fun arg) = succ (size fun + size arg)

-- This term is affine
IsAffine : (t : Term) → Set
IsAffine (var idx)     = Unit
IsAffine (lam bod)     = And (Or (uses bod 0 == 0) (uses bod 0 == 1)) (IsAffine bod)
IsAffine (app fun arg) = And (IsAffine fun) (IsAffine arg)

-- This term is on normal form
IsNormal : (t : Term) → Set
IsNormal (var idx)                 = Unit
IsNormal (lam bod)                 = IsNormal bod
IsNormal (app (var fidx)      arg) = And (IsNormal (var fidx)) (IsNormal arg)
IsNormal (app (lam fbod)      arg) = Empty
IsNormal (app (app ffun farg) arg) = And (IsNormal (app ffun farg)) (IsNormal arg)

-- This term has redexes
HasRedex : (t : Term) → Set
HasRedex (var idx)                 = Empty
HasRedex (lam bod)                 = HasRedex bod
HasRedex (app (var fidx)      arg) = Or (HasRedex (var fidx)) (HasRedex arg)
HasRedex (app (lam fbod)      arg) = Unit
HasRedex (app (app ffun farg) arg) = Or (HasRedex (app ffun farg)) (HasRedex arg)

-- Computes the number of redexes in a term
redexes : (t : Term) → Nat
redexes (var idx)                 = 0
redexes (lam bod)                 = redexes bod
redexes (app (var fidx)      arg) = redexes (var fidx) + redexes arg
redexes (app (lam fbod)      arg) = 1 + (redexes (lam fbod) + redexes arg)
redexes (app (app ffun farg) arg) = redexes (app ffun farg) + redexes arg

-- Directed reduction relation, `a ~> b` means term `a` reduces to `b`
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
subst-miss-size : (n : Nat) → (bidx : Nat) → (arg : Term) → same bidx n == false → size (at n arg bidx) == 0
subst-miss-size (succ n) (succ bidx) arg s = trans (shift-preserves-size succ (at n arg bidx)) (subst-miss-size n bidx arg s)
subst-miss-size (succ n) zero        arg s = refl
subst-miss-size zero     (succ bidx) arg s = refl
subst-miss-size zero     zero        arg ()

-- Helper function 
subst-hit-size : (n : Nat) → (bidx : Nat) → (arg : Term) → same bidx n == true → size (at n arg bidx) == size arg
subst-hit-size (succ n) (succ bidx) arg s = trans (shift-preserves-size succ (at n arg bidx)) (subst-hit-size n bidx arg s)
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
size-after-subst n (var bidx) arg with same bidx n | inspect (same bidx) n
size-after-subst n (var bidx) arg | true  | its e = rwt (λ x → size (at n arg bidx) == x) (sym (add-n-0 (size arg))) (subst-hit-size n bidx arg e)
size-after-subst n (var bidx) arg | false | its e = subst-miss-size n bidx arg e
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
  -- Reducing an affine term can't incrase the amount of times a free variable is used
  reduce-uses : (n : Nat) → (t : Term) → IsAffine t → uses (reduce t) n <= uses t n

-- Reducing an affine term either reduces its size or keeps it the same
reduce<= : (t : Term) → IsAffine t → size (reduce t) <= size t
reduce<= (var idx) af = <=zero zero
reduce<= (lam bod) af = <=succ (reduce<= bod (snd af))
reduce<= (app (var fidx) arg) af = <=succ (reduce<= arg (snd af)) 
reduce<= (app (app ffun farg) arg) af =
  let a = reduce<= (app ffun farg) (fst af)
      b = reduce<= arg (snd af)
      c = <=dist a b
  in  <=succ c
reduce<= (app (lam fbod) arg) af =
  let a = reduce<= fbod (snd (fst af))
      b = reduce<= arg (snd af)
      c = size-after-subst 0 (reduce fbod) (reduce arg)
      d = <=-refl c
      e = reduce-uses 0 fbod (snd (fst af))
      f = <=fct0 e d
  in  case fst (fst af) of λ
      { (or0 o0) →
        let g = rwt (λ x → size (subst (at 0 (reduce arg)) (reduce fbod)) <= (size (reduce fbod) + (x * size (reduce arg)))) o0 f
            h = rwt (λ x → size (subst (at 0 (reduce arg)) (reduce fbod)) <= x) (add-n-0 (size (reduce fbod))) g
            i = <=-trans h a
            j = <=-incr-r (size arg) i
            k = <=-incr-l 1 (<=-incr-l 1 j)
        in k
      ; (or1 o1) →
        let g = rwt (λ x → size (subst (at 0 (reduce arg)) (reduce fbod)) <= (size (reduce fbod) + (x * size (reduce arg)))) o1 f
            h = rwt (λ x → size (subst (at 0 (reduce arg)) (reduce fbod)) <= (size (reduce fbod) + x)) (add-n-0 (size (reduce arg))) g
            i = <=fct1 a h
            j = <=fct2 b i
            k = <=-incr-l 1 (<=-incr-l 1 j)
        in  k
      }

-- Reducing an affine term with redexes reduces its size
-- TODO: this is basically a ctrl+c of the function above with small
-- modifications. Clearly my Agda skills are still needing improvements. How
-- could this be better abstracted?
reduce< : (t : Term) → IsAffine t → HasRedex t → size (reduce t) < size t
reduce< (var idx) af ()
reduce< (lam bod) af hr = <succ (reduce< bod (snd af) hr)
reduce< (app (var fidx) arg) af (or0 ())
reduce< (app (var fidx) arg) af (or1 o1) = <succ (reduce< arg (snd af) o1)
reduce< (app (app ffun farg) arg) af (or0 o0) =
  let a = reduce< (app ffun farg) (fst af) o0
      b = reduce<= arg (snd af)
      c = <<=dist a b
  in  <succ c
reduce< (app (app ffun farg) arg) af (or1 o1) =
  let a = reduce<= (app ffun farg) (fst af)
      b = reduce< arg (snd af) o1
      c = <=<dist a b
  in  <succ c
reduce< (app (lam fbod) arg) af unit =
  let a = reduce<= fbod (snd (fst af))
      b = reduce<= arg (snd af)
      c = size-after-subst 0 (reduce fbod) (reduce arg)
      d = <=-refl c
      e = reduce-uses 0 fbod (snd (fst af))
      f = <=fct0 e d
  in  case fst (fst af) of λ
      { (or0 o0) →
        let g = rwt (λ x → size (subst (at 0 (reduce arg)) (reduce fbod)) <= (size (reduce fbod) + (x * size (reduce arg)))) o0 f
            h = rwt (λ x → size (subst (at 0 (reduce arg)) (reduce fbod)) <= x) (add-n-0 (size (reduce fbod))) g
            i = <=-trans h a
            j = <=-incr-r (size arg) i
            k = <=-incr-l 1 j
        in <=-to-< (<=succ k)
      ; (or1 o1) →
        let g = rwt (λ x → size (subst (at 0 (reduce arg)) (reduce fbod)) <= (size (reduce fbod) + (x * size (reduce arg)))) o1 f
            h = rwt (λ x → size (subst (at 0 (reduce arg)) (reduce fbod)) <= (size (reduce fbod) + x)) (add-n-0 (size (reduce arg))) g
            i = <=fct1 a h
            j = <=fct2 b i
            k = (<=-incr-l 1 j)
        in <=-to-< (<=succ k)
      }

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
