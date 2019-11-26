module EAC where
open import Logic
open import Maybe
open import Nat
open import List
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

infixr 6 _=>_
data Type : Set where
  τ  : Type
  _=>_ : Type -> Type -> Type
  !    : Type -> Type

Context = List Type

-- A proof of x ∈ xs is the index into xs where x is located.
infix 2 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  zero : ∀ {xs} → x ∈ x :: xs
  succ : ∀ {y xs} → x ∈ xs → x ∈ y :: xs

data TermT (Γ : Context) : Type → Set where
  var : ∀ {A} (x : A ∈ Γ) → TermT Γ A
  app : ∀ {A B} → TermT Γ (A => B) → TermT Γ A → TermT Γ B
  lam : ∀ {A B} → TermT (A :: Γ) B → TermT Γ (A => B)
  box : ∀ {A} → TermT Γ A -> TermT Γ (! A)
  dup : ∀ {A B} → TermT Γ (! A) -> TermT (A :: (A :: Γ)) B -> TermT Γ B

rawIndex : ∀ {A} {x : A} {xs} → x ∈ xs → Nat
rawIndex zero    = zero
rawIndex (succ i) = succ (rawIndex i)

eraseTypes : ∀ {Γ A} → TermT Γ A → Term
eraseTypes (var x)   = var $ rawIndex x
eraseTypes (lam t)   = lam $ eraseTypes t
eraseTypes (app s t) = app (eraseTypes s) (eraseTypes t)
eraseTypes (box s)   = box (eraseTypes s)
eraseTypes (dup s t) = app (eraseTypes s) (eraseTypes t)

data WellTyped Γ e : Set where
  ok : (A : Type) (t : TermT Γ A) → eraseTypes t == e → WellTyped Γ e

-- Closed terms that are well-typed
WellTyped* : Term → Set
WellTyped* e = WellTyped [] e

-- Adjusts a renaming function
shift-fn : (Nat -> Nat) -> Nat -> Nat
shift-fn fn zero     = zero
shift-fn fn (succ i) = succ (fn i)

shift-fn-many : Nat -> (Nat -> Nat) -> Nat -> Nat
shift-fn-many n fn = pow shift-fn n fn

-- Renames all free variables with a renaming function, `fn`
shift : (Nat -> Nat) -> Term -> Term
shift fn (var i)       = var $ fn i
shift fn (lam bod)     = lam $ shift (shift-fn fn) bod
shift fn (box bod)     = box $ shift fn bod
shift fn (app fun arg) = app (shift fn fun) (shift fn arg)
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
subst fn (lam bod)     = lam $ subst (subst-fn fn) bod
subst fn (box bod)     = box $ subst fn bod
subst fn (app fun arg) = app (subst fn fun) (subst fn arg)
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

-- Incorrect term
data Incorrect : (t : Term) → Set where
  lam-incorrect : ∀ {bod} → Incorrect bod -> Incorrect (lam bod)
  box-incorrect : ∀ {bod} → Incorrect bod -> Incorrect (box bod)
  app-incorrect : ∀ {fun arg} → Or (Incorrect fun) (Incorrect arg) -> Incorrect (app fun arg)
  dup-incorrect : ∀ {arg bod} → Or (Incorrect arg) (Incorrect bod) -> Incorrect (dup arg bod)
  app-box-incorrect : ∀ {fun arg} → Incorrect (app (box fun) arg)
  dup-lam-incorrect : ∀ {arg bod} → Incorrect (dup (lam arg) bod)

-- Directed one step reduction relation, `a ~> b` means term `a` reduces to `b` in one step
data _~>_ : Term → Term → Set where
  ~beta : ∀ {t u} → app (lam t) u ~> subst (at 0 u) t
  ~app0 : ∀ {a f0 f1} → f0 ~> f1 → app f0 a ~> app f1 a
  ~app1 : ∀ {f a0 a1} → a0 ~> a1 → app f a0 ~> app f a1
  ~lam0 : ∀ {b0 b1} → b0 ~> b1 → lam b0 ~> lam b1

-- Directed arbitraty step reduction relation, `a ~>> b` means term `a` reduces to `b` in zero or more steps
data _~>>_ : Term → Term → Set where
  ~>>refl  : ∀ {t t'} → t == t' → t ~>> t'
  ~>>trans : ∀ {t t' t''} → t ~>> t'' → t'' ~>> t' → t ~>> t'
  ~>>step  : ∀ {t t'} → t ~> t' → t ~>> t'

data Normalizable : (t : Term) → Set where
  normal-is-normalizable : ∀ {t} → IsNormal t → Normalizable t
  onestep-normalizable : ∀ {t t'} → t ~> t' → Normalizable t' → Normalizable t

-- A normal term has no redexes
normal-has-noredex : (t : Term) → IsNormal t → Not (HasRedex t)
normal-has-noredex (lam bod) (lam-normal x) (lam-redex y)                             = normal-has-noredex bod x y
normal-has-noredex (box bod) (box-normal x) (box-redex y)                             = normal-has-noredex bod x y
normal-has-noredex (app (var idx) arg) (app-var-normal x) (app-redex (or1 y))         = normal-has-noredex arg x y
normal-has-noredex (app (app ffun farg) arg) (app-app-normal x _) (app-redex (or0 y)) = normal-has-noredex (app ffun farg) x y
normal-has-noredex (app (app ffun farg) arg) (app-app-normal _ x) (app-redex (or1 y)) = normal-has-noredex arg x y
normal-has-noredex (dup (var idx) bod) (dup-var-normal x) (dup-redex (or1 y))         = normal-has-noredex bod x y
normal-has-noredex (dup (app ffun farg) bod) (dup-app-normal x _) (dup-redex (or0 y)) = normal-has-noredex (app ffun farg) x y
normal-has-noredex (dup (app ffun farg) bod) (dup-app-normal _ x) (dup-redex (or1 y)) = normal-has-noredex bod x y

-- A normal term is correct
normal-correct : (t : Term) → IsNormal t → Not (Incorrect t)
normal-correct (lam bod) (lam-normal x) (lam-incorrect y)                             = normal-correct bod x y
normal-correct (box bod) (box-normal x) (box-incorrect y)                             = normal-correct bod x y
normal-correct (app (var idx) arg) (app-var-normal x) (app-incorrect (or1 y))         = normal-correct arg x y
normal-correct (app (app ffun farg) arg) (app-app-normal x _) (app-incorrect (or0 y)) = normal-correct (app ffun farg) x y
normal-correct (app (app ffun farg) arg) (app-app-normal _ x) (app-incorrect (or1 y)) = normal-correct arg x y
normal-correct (dup (var idx) bod) (dup-var-normal x) (dup-incorrect (or1 y))         = normal-correct bod x y
normal-correct (dup (app ffun farg) bod) (dup-app-normal x _) (dup-incorrect (or0 y)) = normal-correct (app ffun farg) x y
normal-correct (dup (app ffun farg) bod) (dup-app-normal _ x) (dup-incorrect (or1 y)) = normal-correct bod x y

-- A term that has no redexes and is correct is normal
noredex-is-normal : (t : Term) → Not (HasRedex t) → Not (Incorrect t) → IsNormal t
noredex-is-normal (var idx) noredex correct                 = var-normal
noredex-is-normal (lam bod) noredex correct                 = lam-normal (noredex-is-normal bod (noredex ∘ lam-redex) (correct ∘ lam-incorrect))
noredex-is-normal (box bod) noredex correct                 = box-normal (noredex-is-normal bod (noredex ∘ box-redex) (correct ∘ box-incorrect))
noredex-is-normal (app (var idx) arg) noredex correct       = app-var-normal (noredex-is-normal arg (noredex ∘ (app-redex ∘ or1)) (correct ∘ (app-incorrect ∘ or1)))
noredex-is-normal (app (app fun arg') arg) noredex correct =
  app-app-normal
  (noredex-is-normal (app fun arg') (noredex ∘ (app-redex ∘ or0)) (correct ∘ (app-incorrect ∘ or0)))
  (noredex-is-normal arg (noredex ∘ (app-redex ∘ or1)) (correct ∘ (app-incorrect ∘ or1)))
noredex-is-normal (dup (var idx) arg) noredex correct       = dup-var-normal (noredex-is-normal arg (noredex ∘ (dup-redex ∘ or1)) (correct ∘ (dup-incorrect ∘ or1)))
noredex-is-normal (dup (app fun arg') arg) noredex correct  =
  dup-app-normal
  (noredex-is-normal (app fun arg') (noredex ∘ (dup-redex ∘ or0)) (correct ∘ (dup-incorrect ∘ or0)))
  (noredex-is-normal arg (noredex ∘ (dup-redex ∘ or1)) (correct ∘ (dup-incorrect ∘ or1)))
noredex-is-normal (app (dup bod arg') arg) noredex correct  = absurd $ noredex found-app-swap
noredex-is-normal (dup (dup arg' bod) arg) noredex correct  = absurd $ noredex found-dup-swap
noredex-is-normal (dup (box bod) arg) noredex correct       = absurd $ noredex found-dup-redex
noredex-is-normal (app (lam bod) arg) noredex correct       = absurd $ noredex found-app-redex
noredex-is-normal (dup (lam bod) arg) noredex correct       = absurd $ correct dup-lam-incorrect
noredex-is-normal (app (box bod) arg) noredex correct       = absurd $ correct app-box-incorrect

-- A term is either normal or has a redex
normal-or-hasredex : (t : Term) → Or (IsNormal t) (HasRedex t)
normal-or-hasredex (var idx) = or0 var-normal
normal-or-hasredex (lam bod) = case-or (normal-or-hasredex bod) (λ x → or0 (lam-normal x)) (λ x → or1 (lam-redex x))
normal-or-hasredex (app (lam bod) arg) = or1 found-app-redex
normal-or-hasredex (app (var idx) arg) = case-or (normal-or-hasredex arg) (λ x → or0 (app-var-normal x)) (λ x → or1 (app-redex (or1 x)))
normal-or-hasredex (app (app fun arg') arg) =
  case-or (normal-or-hasredex arg)
          (λ x → case-or (normal-or-hasredex (app fun arg'))
                 (λ y → or0 (app-app-normal y x))
                 (λ y → or1 (app-redex (or0 y))))
          (λ x → or1 (app-redex (or1 x)))
normal-or-hasredex x = {!!}

