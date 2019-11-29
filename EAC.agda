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

rawIndex : ∀ {A} {x : A} {xs} → x ∈ xs → Nat
rawIndex zero    = zero
rawIndex (succ i) = succ (rawIndex i)

data ofType (Γ : Context) : Term → Type → Set where
  var : ∀ {A} (x : A ∈ Γ) → ofType Γ (var (rawIndex x)) A
  app : ∀ {A B fun arg} → ofType Γ fun (A => B) → ofType Γ arg A → ofType Γ (app fun arg) B
  lam : ∀ {A B bod} → ofType (A :: Γ) bod B → ofType Γ (lam bod) (A => B)
  box : ∀ {A bod} → ofType Γ bod A -> ofType Γ (box bod) (! A)
  dup : ∀ {A B arg bod} → ofType Γ arg (! A) -> ofType (A :: Γ) bod B -> ofType Γ (dup arg bod) B

WellTyped : Context → Term → Set
WellTyped Γ t = Sum Type (ofType Γ t)

-- Closed terms that are well-typed
WellTyped* : Term → Set
WellTyped* e = WellTyped [] e

-- Renames all free variables by incrementing a value
shift-aux : (idx inc dpt : Nat) -> Nat
shift-aux idx        inc 0          = inc + idx
shift-aux 0          inc (succ dpt) = 0
shift-aux (succ idx) inc (succ dpt) = succ (shift-aux idx inc dpt)

shift : (t : Term) (inc dpt : Nat) -> Term
shift (var i)   inc dpt = var (shift-aux i inc dpt)
shift (lam t)   inc dpt = lam $ shift t inc (1 + dpt)
shift (box t)   inc dpt = box $ shift t inc dpt
shift (app t s) inc dpt = app (shift t inc dpt) (shift s inc dpt)
shift (dup t s) inc dpt = dup (shift t inc dpt) (shift s inc (1 + dpt))

-- Substitutes a free variable on a term with another term
subst : (bod arg : Term) (idx : Nat) → Term
subst (var 0)        arg 0          = arg
subst (var (succ i)) arg 0          = var i
subst (var 0)        arg (succ idx) = var 0
subst (var (succ i)) arg (succ idx) = shift (subst (var i) arg idx) 1 0
subst (lam t)        arg idx        = lam $ subst t arg (1 + idx)
subst (box t)        arg idx        = box $ subst t arg idx
subst (app t s)      arg idx        = app (subst t arg idx) (subst s arg idx)
subst (dup t s)      arg idx        = dup (subst t arg idx) (subst s arg (1 + idx))

-- Lemmas for the cut rule
shift-type-var : ∀ {A Γ i B} → ofType Γ (var i) B → ofType (A :: Γ) (var (succ i)) B
shift-type-var (var pf) = var (succ pf)

shift-type-lemma-aux : ∀ Δ {A Γ t B} → ofType (Δ ++ Γ) t B → ofType (Δ ++ A :: Γ) (shift t 1 (length Δ)) B
shift-type-lemma-aux Δ {A} {Γ} {var _} {B} (var pf)        with Δ
shift-type-lemma-aux Δ {A} {Γ} {var _} {B} (var pf)        | []      = var (succ pf)
shift-type-lemma-aux Δ {A} {Γ} {var _} {B} (var zero)      | C :: Δ' = var zero
shift-type-lemma-aux Δ {A} {Γ} {var _} {B} (var (succ pf)) | C :: Δ' = shift-type-var $ shift-type-lemma-aux Δ' {A} (var pf)
shift-type-lemma-aux Δ {A} {Γ} {lam t} {C => B} (lam pf)             = lam $ shift-type-lemma-aux (C :: Δ) pf
shift-type-lemma-aux Δ {A} {Γ} {box t} { ! B } (box pf)              = box $ shift-type-lemma-aux Δ pf
shift-type-lemma-aux Δ {A} {Γ} {app t s} {B} (app pf_t pf_s)         = app (shift-type-lemma-aux Δ pf_t) (shift-type-lemma-aux Δ pf_s)
shift-type-lemma-aux Δ {A} {Γ} {dup t s} {B} (dup {C} pf_t pf_s)     = dup (shift-type-lemma-aux Δ pf_t) (shift-type-lemma-aux (C :: Δ) pf_s)

shift-type-lemma : ∀ {A Γ t B} → ofType Γ t B → ofType (A :: Γ) (shift t 1 0) B
shift-type-lemma pf = shift-type-lemma-aux [] pf

-- Cut rule
cut_aux : (Δ Γ : Context) (A B : Type) (bod arg : Term) -> ofType (Δ ++ A :: Γ) bod B -> ofType Γ arg A -> ofType (Δ ++ Γ) (subst bod arg (length Δ)) B
cut_aux Δ Γ A B (var _) arg (var pf1) pf2                with rawIndex pf1 | inspect rawIndex pf1
cut_aux [] Γ A A (var _) arg (var zero) pf2              | 0               | its _ = pf2
cut_aux (B :: Δ) Γ A B (var _) arg (var zero) pf2        | 0               | its _ = var zero
cut_aux [] (C :: Γ) A B (var _) arg (var (succ pf1)) pf2 | succ n          | its eq = rwt (λ x → ofType (C :: Γ) (var x) B) (succ-inj eq) (var pf1)
cut_aux (C :: Δ) Γ  A B (var _) arg (var (succ pf1)) pf2 | succ n          | its eq =
   let oftype = rwt (λ x → ofType (Δ ++ Γ) (subst (var x) arg (length Δ)) B) (succ-inj eq) $ cut_aux Δ Γ A B (var _)  arg (var pf1) pf2
   in shift-type-lemma oftype
cut_aux Δ Γ A (C => B) (lam t) arg (lam pf1) pf2      = lam $ cut_aux (C :: Δ) Γ A B t arg pf1 pf2
cut_aux Δ Γ A (! B) (box t) arg (box pf1) pf2         = box $ cut_aux Δ Γ A B t arg pf1 pf2
cut_aux Δ Γ A B (app t s) arg (app {C} pf_t pf_s) pf2 = app (cut_aux Δ Γ A (C => B) t arg pf_t pf2) (cut_aux Δ Γ A C s arg pf_s pf2)
cut_aux Δ Γ A B (dup t s) arg (dup {C} pf_t pf_s) pf2 = dup (cut_aux Δ Γ A (! C) t arg pf_t pf2) (cut_aux (C :: Δ) Γ A B s arg pf_s pf2)

cut : (Γ : Context) (A B : Type) (bod arg : Term) -> ofType (A :: Γ) bod B -> ofType Γ arg A -> ofType Γ (subst bod arg 0) B
cut = cut_aux []

-- Computes how many times a free variable is used
uses : Term -> Nat -> Nat
uses (var idx')    idx with same idx' idx
uses (var idx')    idx | true  = 1
uses (var idx')    idx | false = 0
uses (lam bod)     idx = uses bod (1 + idx)
uses (app fun arg) idx = uses fun idx + uses arg idx
uses (box bod)     idx = uses bod idx
uses (dup arg bod) idx = uses arg idx + uses bod (2 + idx)

uses-n-step : {i n : Nat} -> (p : Nat) -> uses (var (p + i)) (p + n) == uses (var i) n
uses-n-step 0 = refl
uses-n-step (succ p) = uses-n-step p

-- Computes the size of a term
size : Term -> Nat
size (var i)   = 0
size (lam t)   = succ (size t)
size (box t)   = succ (size t)
size (app t s) = succ (size t + size s)
size (dup t s) = succ (size t + size s)

-- Computes the number of redexes in a term
redexes : (t : Term) → Nat
redexes (var i)           = 0
redexes (lam t)           = redexes t
redexes (box t)           = redexes t
redexes (app (var i)   s) = redexes s
redexes (app (lam t)   s) = 1 + (redexes t + redexes s)
redexes (app (app t s) r) = redexes (app t s) + redexes r
redexes (app (dup t s) r) = 1 + (redexes (dup t s) + redexes r)
redexes (dup (var i)   s) = redexes s
redexes (dup (box t)   s) = 1 + (redexes t + redexes s)
redexes (dup (app t s) r) = redexes (app t s) + redexes r
redexes (dup (dup t s) r) = 1 + (redexes (dup t s) + redexes r)
-- should not happen in a typed term
redexes (dup (lam t)   s) = 0
redexes (app (box t)   s) = 0

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

-- Performs a global reduction of all current redexes
reduce : (Γ : Context) (t : Term) (A : Type) -> ofType Γ t A -> Sum Term (λ t → ofType Γ t A)
-- traverses
reduce Γ (var i) A (var pf) = sigma (var i) (var pf)
reduce Γ (lam t) (A => B) (lam pf) =
  let sigma t' pf' = reduce (A :: Γ) t B pf
  in sigma (lam t') (lam pf')
reduce Γ (box t) (! A) (box pf) =
  let sigma t' pf' = reduce Γ t A pf
  in sigma (box t') (box pf')
reduce Γ (app (var i) t) A (app {C} pf1 pf2) =
  let sigma x pf1' = reduce Γ (var i) (C => A) pf1
      sigma t' pf2' = reduce Γ t C pf2
  in sigma (app x t') (app pf1' pf2')
reduce Γ (app (app t s) r) A (app {C} pf1 pf2) =
  let sigma x pf1' = reduce Γ (app t s) (C => A) pf1
      sigma r' pf2' = reduce Γ r C pf2
  in sigma (app x r') (app pf1' pf2')
reduce Γ (dup (var i) t) A (dup {C} pf1 pf2) =
  let sigma x pf1' = reduce Γ (var i) (! C) pf1
      sigma t' pf2' = reduce (C :: Γ) t A pf2
  in sigma (dup x t') (dup pf1' pf2')
reduce Γ (dup (app t s) r) A (dup {C} pf1 pf2) =
  let sigma x pf1' = reduce Γ (app t s) (! C) pf1
      sigma r' pf2' = reduce (C :: Γ) r A pf2
  in sigma (dup x r') (dup pf1' pf2')
-- swaps
reduce Γ (app (dup t s) r) A (app {C} (dup {D} pf1 pf2) pf3) =
  let term = dup t (app s (shift r 1 0))
      type = dup pf1 (app pf2 (shift-type-lemma pf3))
  in sigma term type
reduce Γ (dup (dup t s) r) A (dup {C} (dup {D} pf1 pf2) pf3) =
  let term =  dup t (dup s (shift r 1 1))
      type = dup pf1 (dup pf2 (shift-type-lemma-aux (C :: []) {D} pf3))
  in sigma term type
-- redexes
reduce Γ (app (lam t) s) B (app {A} (lam pf1) pf2) =
  let term = subst t s 0
      type = cut Γ A B t s pf1 pf2
  in sigma term type
reduce Γ (dup (box t) s) B (dup {A} (box pf1) pf2) =
  let term = subst s t 0
      type = cut Γ A B s t pf2 pf1
  in sigma term type

-- Reduce function in a composable form
reduce' : (Γ : Context) (A : Type) -> Sum Term (λ t → ofType Γ t A) -> Sum Term (λ t → ofType Γ t A)
reduce' Γ A (sigma t pf) = reduce Γ t A pf

-- Reduce function but discarding its type
reduce-raw : (Γ : Context) (t : Term) (A : Type) (pf : ofType Γ t A) -> Term
reduce-raw Γ t A pf = Sum.proj1 (reduce Γ t A pf)

-- Elementary affine term
data EAC : (t : Term) → Set where
  var-eac : ∀ {a} → EAC (var a)
  lam-eac : ∀ {bod} → at-level-affine bod 0 0 == true → EAC bod -> EAC (lam bod)
  app-eac : ∀ {fun arg} → EAC fun → EAC arg -> EAC (app fun arg)
  box-eac : ∀ {bod} → EAC bod → EAC (box bod)
  dup-eac : ∀ {arg bod} → at-level bod 0 1 == true → EAC arg → EAC bod → EAC (dup arg bod)

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
normal-has-noredex (lam t) (lam-normal x) (lam-redex y)                       = normal-has-noredex t x y
normal-has-noredex (box t) (box-normal x) (box-redex y)                       = normal-has-noredex t x y
normal-has-noredex (app (var i) t) (app-var-normal x) (app-redex (or1 y))     = normal-has-noredex t x y
normal-has-noredex (app (app t s) r) (app-app-normal x _) (app-redex (or0 y)) = normal-has-noredex (app t s) x y
normal-has-noredex (app (app t s) r) (app-app-normal _ x) (app-redex (or1 y)) = normal-has-noredex r x y
normal-has-noredex (dup (var i) t) (dup-var-normal x) (dup-redex (or1 y))     = normal-has-noredex t x y
normal-has-noredex (dup (app t s) r) (dup-app-normal x _) (dup-redex (or0 y)) = normal-has-noredex (app t s) x y
normal-has-noredex (dup (app t s) r) (dup-app-normal _ x) (dup-redex (or1 y)) = normal-has-noredex r x y

-- A typed term that has no redexes is normal
noredex-is-normal : (Γ : Context) (t : Term) (A : Type) (pf : ofType Γ t A) → Not (HasRedex t) → IsNormal t
noredex-is-normal Γ (var i) A (var _) noredex                     = var-normal
noredex-is-normal Γ (lam t) (A => B) (lam pf) noredex             = lam-normal (noredex-is-normal (A :: Γ) t B pf (noredex ∘ lam-redex))
noredex-is-normal Γ (box t) (! A) (box pf) noredex                = box-normal (noredex-is-normal Γ t A pf (noredex ∘ box-redex))
noredex-is-normal Γ (app (var i) t) A (app {C} _ pf) noredex      = app-var-normal (noredex-is-normal Γ t C pf (noredex ∘ (app-redex ∘ or1)))
noredex-is-normal Γ (app (app t s) r) A (app {C} pf1 pf2) noredex =
  app-app-normal
  (noredex-is-normal Γ (app t s) (C => A) pf1 (noredex ∘ (app-redex ∘ or0)))
  (noredex-is-normal Γ r C pf2 (noredex ∘ (app-redex ∘ or1)))
noredex-is-normal Γ (dup (var i) t) A (dup {C} _ pf) noredex      = dup-var-normal (noredex-is-normal (C :: Γ) t A pf (noredex ∘ (dup-redex ∘ or1)))
noredex-is-normal Γ (dup (app t s) r) A (dup {C} pf1 pf2) noredex =
  dup-app-normal
  (noredex-is-normal Γ (app t s) (! C) pf1 (noredex ∘ (dup-redex ∘ or0)))
  (noredex-is-normal (C :: Γ) r A pf2 (noredex ∘ (dup-redex ∘ or1)))
noredex-is-normal Γ (app (dup _ _) _) A (app _ _) noredex = absurd $ noredex found-app-swap
noredex-is-normal Γ (dup (dup _ _) _) A (dup _ _) noredex = absurd $ noredex found-dup-swap
noredex-is-normal Γ (app (lam _) _)   A (app _ _) noredex = absurd $ noredex found-app-redex
noredex-is-normal Γ (dup (box _) _)   A (dup _ _) noredex = absurd $ noredex found-dup-redex

-- A typed term is either normal or has a redex
normal-or-hasredex : (Γ : Context) (t : Term) (A : Type) (pf : ofType Γ t A) → Or (IsNormal t) (HasRedex t)
normal-or-hasredex Γ (var i) A (var _) = or0 var-normal
normal-or-hasredex Γ (lam t) (A => B) (lam pf) = case-or (normal-or-hasredex (A :: Γ) t B pf) (or0 ∘ lam-normal) (or1 ∘ lam-redex)
normal-or-hasredex Γ (box t) (! A) (box pf) = case-or (normal-or-hasredex Γ t A pf) (or0 ∘ box-normal) (or1 ∘ box-redex)
normal-or-hasredex Γ (app (var i) t) B (app {A} _ pf) = case-or (normal-or-hasredex Γ t A pf) (or0 ∘ app-var-normal) (or1 ∘ (app-redex ∘ or1))
normal-or-hasredex Γ (app (app t s) r) B (app {A} pf1 pf2) =
  case-or (normal-or-hasredex Γ r A pf2)
          (λ x → case-or (normal-or-hasredex Γ (app t s) (A => B) pf1)
                 (λ y → or0 (app-app-normal y x))
                 (λ y → or1 (app-redex (or0 y))))
          (λ x → or1 (app-redex (or1 x)))
normal-or-hasredex Γ (dup (var i) t) B (dup {A} _ pf) = case-or (normal-or-hasredex (A :: Γ) t B pf) (or0 ∘ dup-var-normal) (or1 ∘ (dup-redex ∘ or1))
normal-or-hasredex Γ (dup (app t s) r) B (dup {A} pf1 pf2) =
  case-or (normal-or-hasredex (A :: Γ) r B pf2)
          (λ x → case-or (normal-or-hasredex Γ (app t s) (! A) pf1)
                 (λ y → or0 (dup-app-normal y x))
                 (λ y → or1 (dup-redex (or0 y))))
          (λ x → or1 (dup-redex (or1 x)))
-- swaps
normal-or-hasredex Γ (app (dup t s) r) _ (app _ _) = or1 found-app-swap
normal-or-hasredex Γ (dup (dup t s) r) _ (dup _ _) = or1 found-dup-swap
-- redexes
normal-or-hasredex Γ (app (lam t) s) _ (app _ _) = or1 found-app-redex
normal-or-hasredex Γ (dup (box t) s) _ (dup _ _) = or1 found-dup-redex

-- Directed one step reduction relation, `a ~> b` means term `a` reduces to `b` in one step
data _~>_ : Term → Term → Set where
  ~>lam   : ∀ {t t'}   → t ~> t' → lam t ~> lam t'
  ~>box   : ∀ {t t'}   → t ~> t' → box t ~> box t'
  ~>app0  : ∀ {t t' s} → t ~> t' → app t s ~> app t' s
  ~>app1  : ∀ {t s s'} → s ~> s' → app t s ~> app t s'
  ~>dup0  : ∀ {t t' s} → t ~> t' → dup t s ~> dup t' s
  ~>dup1  : ∀ {t s s'} → s ~> s' → dup t s ~> dup t s'
  ~>beta0 : ∀ {t s}    → app (lam t) s ~> subst t s 0
  ~>beta1 : ∀ {t s}    → dup (box t) s ~> subst s t 0
  ~>swap0 : ∀ {t s r}  → app (dup t s) r ~> dup t (app s (shift r 1 0))
  ~>swap1 : ∀ {t s r}  → dup (dup t s) r ~> dup t (dup s (shift r 1 1))

-- Directed arbitraty step reduction relation, `a ~>> b` means term `a` reduces to `b` in zero or more steps
data _~>>_ : Term → Term → Set where
  ~>>refl  : ∀ {t t'} → t == t' → t ~>> t'
  ~>>trans : ∀ {t t' t''} → t ~>> t'' → t'' ~>> t' → t ~>> t'
  ~>>step  : ∀ {t t'} → t ~> t' → t ~>> t'

data Normalizable : (t : Term) → Set where
  normal : ∀ {t} → IsNormal t → Normalizable t
  step   : ∀ {t t'} → t ~> t' → Normalizable t' → Normalizable t

manystep-norm : ∀ {t t'} → t ~>> t' → Normalizable t' → Normalizable t
manystep-norm (~>>refl refl) norm = norm
manystep-norm (~>>step a)    norm = step a norm
manystep-norm (~>>trans a b) norm = manystep-norm a (manystep-norm b norm)

~>>cong : ∀ {t t'} → (f : Term → Term) → (∀ {t t'} → t ~> t' → f t ~> f t') → t ~>> t' → f t ~>> f t'
~>>cong f pf (~>>refl eq)   = ~>>refl (cong f eq)
~>>cong f pf (~>>trans a b) = ~>>trans (~>>cong f pf a) (~>>cong f pf b)
~>>cong f pf (~>>step a)    = ~>>step (pf a)

~>>pow : (f : Term → Term) → (∀ {x} → x ~>> f x) → ∀ {x} n → x ~>> pow f n x
~>>pow f pf 0 = ~>>refl refl
~>>pow f pf (succ n) = ~>>trans (~>>pow f pf n) pf

reduce-~>> : {Γ : Context} {t : Term} {A : Type} {pf : ofType Γ t A} → t ~>> reduce-raw Γ t A pf
reduce-~>> {Γ} {var i}           {A} {var pf} = ~>>refl refl
reduce-~>> {Γ} {lam t}           {A} {lam pf} = ~>>cong lam ~>lam reduce-~>>
reduce-~>> {Γ} {box t}           {A} {box pf} = ~>>cong box ~>box reduce-~>>
reduce-~>> {Γ} {app (var i) s}   {A} {app (var pf1) pf2} = ~>>cong (app (var i)) ~>app1 reduce-~>>
reduce-~>> {Γ} {app (lam t) s}   {A} {app {C} (lam pf1) pf2} = ~>>step ~>beta0
reduce-~>> {Γ} {app (app t s) r} {A} {app {C} (app pf1 pf2) pf3} = let
  part0 = ~>>cong (app (app t s)) ~>app1 reduce-~>>
  part1 = ~>>cong (λ x → app x (reduce-raw Γ r C pf3)) ~>app0 (reduce-~>> {Γ} {app t s} {C => A} {app pf1 pf2})
  in ~>>trans part0 part1
reduce-~>> {Γ} {app (dup t s) r} {A} {app {C} (dup pf1 pf2) pf3} = ~>>step ~>swap0
reduce-~>> {Γ} {dup (var i) s}   {A} {dup (var pf1) pf2} = ~>>cong (dup (var i)) ~>dup1 reduce-~>>
reduce-~>> {Γ} {dup (box t) s}   {A} {dup {C} (box pf1) pf2} = ~>>step (~>beta1 {t} {s})
reduce-~>> {Γ} {dup (app t s) r} {A} {dup {C} (app pf1 pf2) pf3} = let
  part0 = ~>>cong (dup (app t s)) ~>dup1 reduce-~>>
  part1 = ~>>cong (λ x → dup x (reduce-raw (C :: Γ) r A pf3)) ~>dup0 (reduce-~>> {Γ} {app t s} { ! C } {app pf1 pf2})
  in ~>>trans part0 part1
reduce-~>> {Γ} {dup (dup t s) r} {A} {dup {C} (dup pf1 pf2) pf3} = ~>>step ~>swap1
