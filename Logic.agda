module Logic where

-- This enables the "case-of idiom", which isn't built-in
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

-- Empty set
data Empty : Set where

absurd : {A : Set} -> Empty -> A
absurd ()

Not : Set -> Set
Not A = A -> Empty

modus-tollens : {A B : Set} -> (A -> B) -> (Not B -> Not A)
modus-tollens f nb a = nb (f a)

-- Set with one element
data Unit : Set where
  unit : Unit

-- Set with two elements
data Bool : Set where
  true  : Bool
  false : Bool
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

_&&_ : Bool -> Bool -> Bool
false && _ = false
true && x = x

_||_ : Bool -> Bool -> Bool
true || _ = true
false || x = x

-- Simple pairs (a.k.a., logical And)
record And (A : Set) (B : Set) : Set where
  constructor and
  field
    fst : A
    snd : B

-- Simple disjunctions (a.k.a. logical Or)
data Or (A : Set) (B : Set) : Set where
  or0 : (a : A) → Or A B
  or1 : (b : B) → Or A B

-- Dependent elimination
d-case-or : {A B : Set} {C : Or A B -> Set} ->
            (m : (Or A B)) -> 
            ((a : A) -> C (or0 a)) ->
            ((b : B) -> C (or1 b)) ->
            C m
d-case-or (or0 a) inj0 inj1 = inj0 a
d-case-or (or1 b) inj0 inj1 = inj1 b

-- Nondependent elimination
case-or : {A B C : Set} -> Or A B -> (A -> C) -> (B -> C) -> C
case-or {A} {B} {C} x f g = d-case-or {A} {B} {\ x -> C} x f g

record Sum (A : Set) (B : A → Set) : Set where
  constructor sigma
  field
    proj1 : A
    proj2 : B proj1

-- Function composition
_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

-- Application
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
