--------- PART 1 -----------
-- ! : in Agda is the same as :: in Haskell (of type)
data Nat : Set where
    zero : Nat
    suc : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero + y = y
(suc n) + y = suc (n + y)

_*_ : Nat → Nat → Nat
zero * y = zero
suc x * y = (x * y) + y

data Bool : Set where
    true : Bool
    false : Bool

not : Bool → Bool
not true = false
not false = true

_&&_ : Bool → Bool → Bool
true && b = b
false && _ = false

_||_ : Bool → Bool → Bool
true || b = true
false || b = b

even : Nat → Bool
even zero = true
even (suc n) = false

-- Types in Agda are first-class citizens
-- can be used as values to be returned or passed around
-- type of Nat, Bool is Set

-- This is like a type alias: type MyNat = Nar
MyNat : Set
MyNat = Nat

-- This also allows polymorphic functions:
-- type A (of type Set) is an argument
id : (A : Set) → A → A
id A x = x
-- id Bool true = true

-- we abstract this by curly braces, ignoring type args
id' : {A : Set} → A → A
id' x = x

-- polymorphic datatypes
data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A -- :: is like cons in Haskell

-- tuple in Agda
data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B
    
fst : {A B : Set} → A × B → A 
fst (x , y) = x

snd : {A B : Set} → A × B → B 
snd (x , y) = y

length : {A : Set} → List A → Nat
length [] = 0
length (a :: as) = 1 + length as

_++_ : {A : Set} → List A → List A → List A
[] ++ bs = bs
(x :: as) ++ bs = x :: (as ++ bs)

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs


data Maybe (A : Set) : Set where
    just : A → Maybe A
    nothing : Maybe A

lookup : {A : Set} → List A → Nat → Maybe A
lookup [] _ = nothing
lookup (x :: xs) zero = just x
lookup (x :: xs) (suc n) = lookup xs n

-- Agda functions are total functions:
-- no error or undefined
-- all definitions are terminating


----------- Part 2 ------------
-- dependent types refer to parts of a program
-- used to encode program invariants
-- a return type of a function may depend on the input to a function

-- an argument to a function may be made implicit (using {})
-- if that argument appears in the type of a later argument

-- overloaded constructors [] and ::
-- type of Vec is Nat → Set
-- Nat here is the index
data Vec (A : Set) : Nat → Set where
    [] : Vec A 0
    _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)
infixr 5 _::_

downFrom : (n : Nat) → Vec Nat n
downFrom 0 = []
downFrom (suc n) = n :: downFrom n

-- Here, the type depends on both m and n
_++Vec_ : {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
[] ++Vec ys = ys
(x :: xs) ++Vec ys = x :: (xs ++Vec ys)

-- head takes type Vec A (suc n)
-- Therefore, the vector length cannot be 0
head : {A : Set} {n : Nat} → Vec A (suc n) → A 
head (x :: xs) = x

tail : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail (x :: xs) = xs

-- finite set of integers (naturals) up to n - 1
-- zero n constructs Fin (suc n), because Fin (suc n) goes up to n
-- suc n constructs Fin (suc n) from Fin n
-- this is the family of Fin types
data Fin : Nat → Set where
    zero : {n : Nat} → Fin (suc n)
    suc : {n : Nat} → Fin n → Fin (suc n)

-- with Fin, we can create a safe lookup for vectors
-- the type Fin 0 has no possible element, so n > 0
-- this is a safe and total function
lookupVec : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookupVec (x :: xs) zero = x
lookupVec (x :: xs) (suc n) = lookupVec xs n

putVec : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
putVec zero a (x :: xs) = a :: xs
putVec (suc n) a (x :: xs) = x :: putVec n a xs


-- dependent pair type: \Sigma 
-- a pair type A × B where the second component B
-- can depend on the first component A
data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (x : A) → B x → Σ A B
-- the second parameter (B : A → Set) is a dependent type

-- We can create regular pair type
-- by ignoring the input for the second parameter
-- this is a type alias
_×'_ : (A B : Set) → Set 
A ×' B = Σ A (λ _ → B)

conv1 : (A B : Set) → Set → Set
conv1 A ×' B = A × B

conv2 : (A B : Set) → Set → Set
conv2 A × B = A ×' B 

fstΣ : {A : Set} {B : A → Set} → Σ A B → A 
fstΣ (x , y) = x

-- The return type of sndΣ depends on the on the result of the first type
sndΣ : {A : Set} {B : A → Set} → (z : Σ A B) → B (fstΣ z)
sndΣ (x , y) = y



-- Curry-Howard correspondence tells us:
-- We can interpret logical propositions
-- as types whose elements are proofs of the proposition

-- Conjunction: P and Q
-- we need something of type P and something of type Q
-- corresponds to pair type P × Q

-- Implication: P => Q
-- corresponds to function of type P → Q
-- We assume we have an x of type P
-- with that we need to construct q of type Q
-- λ x → q

-- Disjunction: P or Q
-- we need p of type P or q of type Q
-- left p or right q
-- we uses cases z f g to prove for each of p, q
-- corresponds to type Either P Q

-- Truth
-- This is simply the unit type with one inhabitant, like () in Haskell
-- ⊤

-- False
-- ⊥ has no constructors

-- Negation: not P
-- P → ⊥

-- Equivalence: P <=> Q
-- (P → Q) × (Q → P)
-- is as P implies Q and Q implies P

data Either (A B : Set) : Set where
    left : A → Either A B
    right : B → Either A B

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left x) f g = f x
cases (right x) f g = g x

-- proving P implies P
proof1 : (P : Set) → P → P
proof1 P = id P

-- proving (P implies Q) and (Q implies R) implies (P implies R)
proof2 : {P Q R : Set} → (P → Q) × (Q → R) → (P → R)
proof2 (f , g) p = g (f p)
-- proof2 (f , g) = λ p → g (f p)

-- proving that ((P or Q) implies R) implies (P implies R) and (Q implies R)
proof3 : {P Q R : Set} → (Either P Q → R) → (P → R) × (Q → R)
proof3 f = (λ x → f (left x)) , (λ y → f (right y))