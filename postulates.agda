module postulates where

postulate A : Set
postulate B : Set
postulate f : A → B
postulate a : A

-- Construct a value of type B by applying f
-- This is the only way to get something of type B
b : B
b = f a

-- Check that two functions are the same
-- This only typechecks if the two functions are the same
-- due to the theory of uninterpreted functions
g g' : A → A
g = λ a → a
g' a = a

postulate P : (A → A) → Set
h : P g → P g'
h x = x

-- Propositions as types
-- Define types to be propositions; the proposition
-- is true if we can find a witness (a value of that type,
-- which also serves as a proof of the proposition)

-- Postulates are considered atomic formulas; cannot
-- reduce them further, and do not assume anything
-- about their value. If we postulate a : A, then we
-- postulate that A is true. We can also think of them
-- as symbolic variables, or uninterpreted functions.

-- Types are similar to propositional variables, e.g.,
-- in ((A ∧ B) ∨ C)

-- Example with postulates:
-- Note that we interpret the Person Set as a type,
-- but we can interpret the (IsStudent mary) Set
-- as a proposition, for which we have a witness
-- (maryIsStudent)
postulate Person : Set
postulate john : Person
postulate mary : Person
postulate IsStudent : Person → Set
postulate maryIsStudent : IsStudent mary

-- With this postulate, it is possible to construct
-- a proof of (IsStudent john) and therefore prove it
postulate implication : IsStudent mary → IsStudent john

proofJohnIsStudent : IsStudent john
proofJohnIsStudent = implication maryIsStudent

-- Correspondence of logic to programming:
-- A → B is a function mapping (proofs of) A to (proofs of) B
-- If we have a value (a : A) and a function (a-b : A → B),
-- then we can prove B with (b : a-b a)

-- Sample proof of the above; i.e.,:
-- A → (A → B) → B
postulate C D : Set
postulate c : C
postulate c-d : C → D

proof1 : (C → D) → C → D
proof1 c-d c = c-d c

-- Sample proof of A → A
variable
  F : Set
  
id : F → F
id x = x

proof2 : (C → D) → C → D
proof2 = id
