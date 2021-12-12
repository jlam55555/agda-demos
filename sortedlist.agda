module sortedlist where

-- Agda: where proving and programming are one and the same
-- Based in dependent type theory

-- Simple example in Agda: natural numbers
data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

-- Define a function on the new type we just defined.
-- (This is pretty typical functional programming.)
_+_ : ℕ → ℕ → ℕ
n + Z = n
n + S m = S (n + m)

-- Example of the reduction system: can perform normal calculations
-- by conceptually substituting values
e1 : ℕ
e1 = S Z + (S (S Z))

-- Dependent types essentially allow us to have types that are
-- parameterized on values as well as other types.

-- E.g., SortedList is dependent on the list values
-- sort : NatList → SortedList
-- type SortedList = (l : NatList) × (_ : Sorted l)
-- Technically, we should also check that the result has the
-- same elements as the inputs, thus:
-- sort : (l : NatList) → ((l' : NatList) × (Sorted l') × (EqElems l l'))

-- Here so we don't have to redefine natural numbers
-- and so we can use numeric literals
open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- Essentially symbolic variables
variable
  A B C : Set
  x y z : A
  k l m n : Nat

-- Basic definition of a List based on cons cells
-- https://plfa.github.io/Lists/
data List : (A : Set) → Set where
  [] : List A
  _::_ : A → List A → List A

-- x ≤ y is a proof indexed on x, y
-- It is only true if it is constructable, i.e., there is a witness
-- https://jesper.sikanda.be/posts/formalize-all-the-things.html
data _≤_ : Nat → Nat → Set where
  ≤-zero : zero ≤ n
  ≤-suc : m ≤ n → suc m ≤ suc n

p1 : 3 ≤ 5
p1 = ≤-suc (≤-suc (≤-suc ≤-zero))

-- A proof that x is less than all values in xs
-- https://www.twanvl.nl/blog/agda/sorting
-- x is less than all values in xs if x is less than the head of xs
-- and x is less than all values in the tail of xs
data _≤*_ : (x : Nat) → List Nat → Set where
  [] : x ≤* []
  _::_ : ∀ {y ys} → (x ≤ y) → x ≤* ys → x ≤* (y :: ys)

p2 : 0 ≤* (1 :: [])
p2 = ≤-zero :: []

-- A proof that a list is sorted
-- A list is sorted if the head is less than all elements of the tail,
-- and the tail is sorted
data Sorted : (List Nat) → Set where
  [] : Sorted []
  _::_ : ∀ {x xs} → x ≤* xs → Sorted xs → Sorted (x :: xs)

lst : List Nat
lst = 2 :: (3 :: (5 :: []))

-- Interactive theorem proving!!!!!
p3 : Sorted lst
p3 = ((≤-suc (≤-suc ≤-zero)) :: ((≤-suc (≤-suc ≤-zero)) :: [])) :: (((≤-suc (≤-suc (≤-suc ≤-zero))) :: []) :: ([] :: []))
