open import Equality

module EquationalReasoning {A : Set} where

  infix  1 begin_
  infixr 2 _==<>_ _==<_>_
  infix  3 _qed

  begin_ : ∀ {x y : A}
    → x == y
      -----
    → x == y
  begin x==y  =  x==y

  _==<>_ : ∀ (x : A) {y : A}
    → x == y
      -----
    → x == y
  x ==<> x==y  =  x==y

  _==<_>_ : ∀ (x : A) {y z : A}
    → x == y
    → y == z
      -----
    → x == z
  x ==< x==y > y==z  =  trans x==y y==z

  _qed : ∀ (x : A)
      -----
    → x == x
  x qed  =  refl
