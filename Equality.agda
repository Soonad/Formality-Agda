module Equality where

-- Propositional equality
data _==_ {A : Set} (x : A) : (y : A) → Set where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}

-- Congruence of equality
cong : {A B : Set} → (f : A -> B) → {x y : A} → (e : x == y) → f x == f y
cong f refl = refl

-- Symmetry of equality
sym : {A : Set} → {x y : A} → (e : x == y) → y == x
sym refl = refl

-- Transitivity of equality
trans : {A : Set} {x y z : A} → (xy : x == y) → (yz : y == z) → x == z
trans refl yz = yz

-- Rewrites equal terms on types
rwt : {A : Set} → (P : A -> Set) → {x y : A} → (e : x == y) → (p : P x) → P y
rwt P refl p = p

-- Leibniz rule
leibniz : {A : Set} (x y : A) -> ((P : A -> Set) -> P x -> P y) -> x == y
leibniz a b H = H (_==_ a) refl
