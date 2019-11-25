module EAC where
open import Logic
open import Maybe
open import Nat
open import Equality
open import EquationalReasoning

-- ::::::::::::::
-- :: Language ::
-- ::::::::::::::

-- A λ-calculus term. We're keeping types as simple as possible, so we don't
-- keep a Fin index tracking free vars, nor contexts in any form
data Term : Set where
  var : Nat -> Term
  lam : Term -> Term
  app : Term -> Term -> Term
  box : Term -> Term
  dup : Term -> Term -> Term

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
shift fn (box bod)     = box (shift fn bod)
shift fn (dup arg bod) = dup (shift fn arg) (shift (shift-fn (shift-fn fn)) bod)

-- Adjusts a substitution map
subst-fn : (Nat → Term) → Nat → Term
subst-fn fn zero     = var zero
subst-fn fn (succ i) = shift succ (fn i)

-- Creates a substitution map that replaces only one variable
at : Nat → Term → Nat → Term
at zero     term zero     = term
at zero     term (succ i) = var i
at (succ n) term = subst-fn (at n term)

-- Substitutes all free vars on term with a substitution map, `fn`
subst : (Nat -> Term) -> Term -> Term
subst fn (var i)       = fn i
subst fn (lam bod)     = lam (subst (subst-fn fn) bod)
subst fn (app fun arg) = app (subst fn fun) (subst fn arg)
subst fn (box bod)     = box (subst fn bod)
subst fn (dup arg bod) = dup (subst fn arg) (subst (subst-fn (subst-fn fn)) bod)

-- Computes how many times a free variable is used
uses : Term -> Nat -> Nat
uses (var idx')    idx with same idx' idx
uses (var idx')    idx | true  = 1
uses (var idx')    idx | false = 0
uses (lam bod)     idx = uses bod (1 + idx)
uses (app fun arg) idx = uses fun idx + uses arg idx
uses (box bod)     idx = uses bod idx
uses (dup arg bod) idx = uses arg idx + uses bod (2 + idx)

-- Checks whether all occurences of a free variable are in a specific level
at-level-aux : Nat -> Term -> Nat -> Nat -> Bool
at-level-aux current-lvl (var idx')    idx lvl with same idx' idx
at-level-aux current-lvl (var idx')    idx lvl | true  = same current-lvl lvl
at-level-aux current-lvl (var idx')    idx lvl | false = true
at-level-aux current-lvl (lam bod)     idx lvl = at-level-aux current-lvl bod (1 + idx) lvl
at-level-aux current-lvl (app fun arg) idx lvl = at-level-aux current-lvl fun idx lvl && at-level-aux current-lvl arg idx lvl
at-level-aux current-lvl (box bod)     idx lvl = at-level-aux (succ current-lvl) bod idx lvl
at-level-aux current-lvl (dup bod arg) idx lvl = at-level-aux current-lvl bod idx lvl && at-level-aux current-lvl bod (2 + idx) lvl

at-level : Term -> Nat -> Nat -> Bool
at-level term idx lvl = at-level-aux 0 term idx lvl

at-level-affine : Term -> Nat -> Nat -> Bool
at-level-affine term idx lvl with uses term idx
at-level-affine term idx lvl | 0 = true
at-level-affine term idx lvl | 1 = at-level term idx lvl
at-level-affine term idx lvl | succ (succ _) = false

data EAC : (t : Term) → Set where
  var-eac : ∀ {a} → EAC (var a)
  lam-eac : ∀ {bod} → at-level-affine bod 0 0 == true → EAC bod -> EAC (lam bod)
  app-eac : ∀ {fun arg} → EAC fun → EAC arg -> EAC (app fun arg)
  box-eac : ∀ {bod} → EAC bod → EAC (box bod)
  dup-eac : ∀ {arg bod} → at-level-affine bod 0 1 == true → at-level-affine bod 1 1 == true → EAC arg → EAC bod → EAC (dup arg bod)

-- Performs a global reduction of all current redexes
reduce : Term -> Maybe Term
-- traverses
reduce (var i)                   = (| (var i) |)
reduce (lam bod)                 = (| lam (reduce bod) |)
reduce (box bod)                 = (| box (reduce bod) |)
reduce (app (var idx) arg)       = (| (app (var idx)) (reduce arg) |)
reduce (app (app ffun farg) arg) = (| app (reduce (app ffun farg)) (reduce arg) |)
reduce (dup (var idx) bod)       = (| (dup (var idx)) (reduce bod) |)
reduce (dup (app fun arg) bod)   = (| dup (reduce (app fun arg)) (reduce bod) |)
-- swaps
reduce (app (dup arg arg') bod)  = (| (dup arg (app arg' (shift (2 +_) bod))) |)
reduce (dup (dup arg arg') bod)  = (| (dup arg (dup arg' (shift (2 +_) bod))) |)
-- redexes
reduce (app (lam bod) arg)       = (| (subst (at zero arg) bod) |)
reduce (dup (box arg) bod)       = (| (subst (at zero arg) (subst (at zero arg) bod)) |)
-- should not happen
reduce (app (box bod) arg)       = none
reduce (dup (lam bod') bod)      = none

-- This term is on normal form
data IsNormal : (t : Term) → Set where
  var-normal : ∀ {a} → IsNormal (var a)
  lam-normal : ∀ {bod} → IsNormal bod -> IsNormal (lam bod)
  box-normal : ∀ {bod} → IsNormal bod -> IsNormal (box bod)
  app-var-normal : ∀ {fidx arg} → IsNormal arg -> IsNormal (app (var fidx) arg)
  app-app-normal : ∀ {ffun farg arg} → IsNormal (app ffun farg) → IsNormal arg -> IsNormal (app (app ffun farg) arg)
  dup-var-normal : ∀ {fidx arg} → IsNormal arg -> IsNormal (dup (var fidx) arg)
  dup-app-normal : ∀ {ffun farg arg} → IsNormal (app ffun farg) → IsNormal arg -> IsNormal (dup (app ffun farg) arg)

-- This term has redexes
data HasRedex : (t : Term) → Set where
  lam-redex : ∀ {bod} → HasRedex bod -> HasRedex (lam bod)
  box-redex : ∀ {bod} → HasRedex bod -> HasRedex (box bod)
  app-redex : ∀ {fun arg} → Or (HasRedex fun) (HasRedex arg) -> HasRedex (app fun arg)
  dup-redex : ∀ {arg bod} → Or (HasRedex arg) (HasRedex bod) -> HasRedex (dup arg bod)
  found-app-redex : ∀ {bod arg} → HasRedex (app (lam bod) arg)
  found-dup-redex : ∀ {bod arg} → HasRedex (dup (box bod) arg)
  found-app-swap : ∀ {bod arg arg'} → HasRedex (app (dup arg arg') bod)
  found-dup-swap : ∀ {bod arg arg'} → HasRedex (dup (dup arg arg') bod)

-- A normal term has no redexes
normal-has-noredex : (t : Term) → IsNormal t → Not (HasRedex t)
normal-has-noredex (lam bod) (lam-normal bod-isnormal) (lam-redex bod-hasredex) = normal-has-noredex bod bod-isnormal bod-hasredex
normal-has-noredex (box bod) (box-normal bod-isnormal) (box-redex bod-hasredex) = normal-has-noredex bod bod-isnormal bod-hasredex
normal-has-noredex (app (var idx) arg) (app-var-normal arg-isnormal) (app-redex (or1 arg-hasredex)) = normal-has-noredex arg arg-isnormal arg-hasredex
normal-has-noredex (app (app ffun farg) arg) (app-app-normal fun-isnormal _) (app-redex (or0 fun-hasredex)) = normal-has-noredex (app ffun farg) fun-isnormal fun-hasredex
normal-has-noredex (app (app ffun farg) arg) (app-app-normal _ arg-isnormal) (app-redex (or1 arg-hasredex)) = normal-has-noredex arg arg-isnormal arg-hasredex
normal-has-noredex (dup (var idx) bod) (dup-var-normal bod-isnormal) (dup-redex (or1 bod-hasredex)) = normal-has-noredex bod bod-isnormal bod-hasredex
normal-has-noredex (dup (app ffun farg) bod) (dup-app-normal fun-isnormal _) (dup-redex (or0 fun-hasredex)) = normal-has-noredex (app ffun farg) fun-isnormal fun-hasredex
normal-has-noredex (dup (app ffun farg) bod) (dup-app-normal _ bod-isnormal) (dup-redex (or1 bod-hasredex)) = normal-has-noredex bod bod-isnormal bod-hasredex
