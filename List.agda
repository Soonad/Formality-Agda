module List where

open import Nat
open import Logic

infixr 50 _::_ _++_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _::_ #-}

length : {A : Set} -> List A -> Nat
length []        = 0
length (_ :: xs) = 1 + length xs

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

zipWith : {A B C : Set} -> (A -> B -> C) -> List A -> List B -> List C
zipWith f []        []        = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys
zipWith f []        (_ :: _)  = []
zipWith f (_ :: _)  []        = []

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f z []        = z
foldr f z (x :: xs) = f x (foldr f z xs)

foldl : {A B : Set} -> (B -> A -> B) -> B -> List A -> B
foldl f z []        = z
foldl f z (x :: xs) = foldl f (f z x) xs

replicate : {A : Set} -> Nat -> A -> List A
replicate  zero   x = []
replicate (succ n) x = x :: replicate n x

iterate : {A : Set} -> Nat -> (A -> A) -> A -> List A
iterate  zero   f x = []
iterate (succ n) f x = x :: iterate n f (f x)

reverse : {A : Set} -> List A -> List A
reverse xs = foldl (λ xs x → x :: xs) [] xs

splitAt : {A : Set} -> Nat -> List A -> And (List A) (List A)
splitAt  zero   xs        = and [] xs
splitAt (succ n) []        = and [] []
splitAt (succ n) (x :: xs) = add x $ splitAt n xs
  where
    add : _ -> And (List _) (List _) -> And (List _) (List _)
    add x (and ys zs) = and (x :: ys) zs

