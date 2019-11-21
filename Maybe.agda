data Maybe (A : Set) : Set where
  none : Maybe A
  just : A -> Maybe A

_>>=_ : ∀ {A B} → Maybe A → (A → Maybe B) → Maybe B
none   >>= f = none
just x >>= f = f x

_>>_ : ∀ {A B} → Maybe A → Maybe B → Maybe B
none   >> m = none
just x >> m = m

pure  : ∀ {A} → A → Maybe A
pure = just

_<*>_ : ∀ {A B} → Maybe (A → B) → Maybe A → Maybe B
none <*> _ = none
just f <*> none = none
just f <*> just a = just (f a)
