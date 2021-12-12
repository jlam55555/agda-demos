module disjointunion where

-- Abstract disjoint (tagged) union
data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

-- Note that this function can even return
-- different types depending on if the input
-- is left or right (the output type is a function
-- of the input values)
Case-+ : {A B : Set}
  → {C : (A + B) → Set}
  → ((a : A) → C (inl a))
  → ((b : B) → C (inr b))
  → (d : A + B)
  → C d
Case-+ case-inl _ (inl a) = case-inl a
Case-+ _ case-inr (inr b) = case-inr b

-- Use of concrete disjoint unions: variant types
postulate Tree Flower : Set
data Bool : Set where
  tt ff : Bool

data Plant : Set where
  tree : Tree → Plant
  flower : Flower → Plant

isFlower : Plant → Bool
isFlower (tree _) = ff
isFlower (flower _) = tt

-- Use of disjoint union in disjunction (∨)
-- A ∨ B is true iff. A is true or B is true
-- A proof of A ∨ B comprises a proof of either A
-- or a proof of B, along with the information with
-- which one. Thus A ∨ B is equivalent to A + B.
data _∨_ (A B : Set) : Set where
  or1 : A → A ∨ B
  or2 : B → A ∨ B

-- Sample derivation: (A ∨ B) → (B ∨ A)
postulate A B : Set
lemma3 : A ∨ B → B ∨ A
lemma3 (or1 a) = or2 a
lemma3 (or2 b) = or1 b
