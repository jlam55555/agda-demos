module bools where

-- Formation and introduction rules:
-- type and term constructors
data Bool : Set where
  tt ff : Bool

-- Elimination and equality rules
-- Eliminating a variable (b : Bool)
-- Note also: implicit argument (C : Bool → Set) since
-- this value can be inferred
CaseBool : {C : Bool → Set} → C tt → C ff → (b : Bool) → C b
CaseBool casett caseff b with b
... | tt = casett
... | ff = caseff

-- Alternatively:
CaseBool' : (C : Bool → Set) → C tt → C ff → (b : Bool) → C b
CaseBool' C casett _ tt = casett
CaseBool' C _ caseff ff = caseff

-- Sample usage
data FemaleName : Set where
  sara : FemaleName
data MaleName : Set where
  tom : MaleName

Name : Bool → Set
Name tt = FemaleName
Name ff = MaleName

SelectBool : (b : Bool) → Name b
SelectBool tt = sara
SelectBool ff = tom
