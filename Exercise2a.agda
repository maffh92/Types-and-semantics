
module Exercise2a where

--------------------------------------------------------------------------------
--Instructions--
{-

This exercise consists of two parts.  

1. Firstly, complete the missing definitions. You may want to check the
previous version of some lemmas and definitions (BoolDemo.agda) in
case you get stuck.

Note that in many of the lemmas, I have made all arguments
explicit. This way I don't give away too much information about how to
do your induction. In many cases, you can make many of these arguments
implicit - feel free to do so!

2. Extend the Term data type with constructors for creating tuples,
fst, and snd. Update the various semantics accordingly, and complete
the proofs.

You may want to check Chapter 11.7 of Pierce's book to see how he defines
the syntax, semantics and types for tuples.

-}
--------------------------------------------------------------------------------



-------------------------------------------------------------------------------
----------------------                 Prelude             --------------------
-------------------------------------------------------------------------------

-- Equality.
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x
  
cong : {a b : Set} {x y : a} (f : a -> b) -> x == y -> f x == f y
cong f refl = refl

-- Contradiction type.
data Empty : Set where

-- Reducto ab absurdum.
contradiction : {A : Set} → Empty → A
contradiction ()

data Exists (a : Set) (b : a -> Set) : Set where
  Witness : (x : a) -> b x -> Exists a b


-- Negation
Not : Set → Set
Not A = A → Empty

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

data Either (a b : Set) : Set where
  Left : a -> Either a b
  Right : b -> Either a b

-------------------------------------------------------------------------------
----------------------                Syntax             ----------------------
-------------------------------------------------------------------------------

data Type : Set where
  NAT : Type 
  BOOL : Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : forall {σ} -> (c : Term BOOL) -> (t e : Term σ) → Term σ
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And what else?
  vnat : Nat -> Value NAT


-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat Zero ⌝ = zero
⌜ vnat (Succ x) ⌝ = succ ⌜ vnat x ⌝ 

------------------------------------------------------------------------
-- Denotational semantics.
--------------------------------------------------------------------------------


-- Evaluation function.
⟦_⟧ : forall {ty} ->  Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ with ⟦ t ⟧
⟦ if t then t₁ else t₂ ⟧ | vtrue = ⟦ t₁ ⟧
⟦ if t then t₁ else t₂ ⟧ | vfalse = ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ t ⟧ with ⟦ t ⟧
⟦ succ t ⟧ | vnat x = vnat (Succ x)
⟦ iszero t ⟧ with ⟦ t ⟧
⟦ iszero t ⟧ | vnat Zero = vtrue
⟦ iszero t ⟧ | vnat (Succ x) = vfalse



-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data IsValue : {ty : Type} -> Term ty -> Set where
  V-True : IsValue true
  V-False : IsValue false
  V-Zero : IsValue zero
  V-Succ : ∀ {x} -> IsValue x -> IsValue (succ x)

isValueComplete : forall {ty} -> (v : Value ty) -> IsValue ⌜ v ⌝ 
isValueComplete vtrue = V-True
isValueComplete vfalse = V-False
isValueComplete (vnat Zero) = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))

isValueSound : forall {ty} {t : Term ty} -> IsValue t -> Exists (Value ty) (\v -> ⌜ v ⌝ == t)
isValueSound V-True = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero = Witness (vnat Zero) refl
isValueSound (V-Succ p) with isValueSound p
isValueSound (V-Succ p) | Witness (vnat k) q = Witness (vnat (Succ k) ) (cong succ q)

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ : forall {t t' : Term NAT} -> Step t t' -> Step (succ t) (succ t') 
  E-IsZeroZero : Step (iszero zero) true
  E-IsZeroSucc : ∀ {t : Term NAT} -> IsValue t -> Step (iszero (succ t)) false
  E-IsZero : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')

preservation : ∀ {ty} -> (t t' : Term ty) -> Step t t' -> ty == ty
preservation t t' step = refl

valuesDoNotStep : forall {ty} -> (t t' : Term ty) -> Step t t' -> IsValue t -> Empty
valuesDoNotStep .true t' () V-True
valuesDoNotStep .false t' () V-False
valuesDoNotStep .zero t' () V-Zero
valuesDoNotStep ._ ._ (E-Succ x₁) (V-Succ x₂) = valuesDoNotStep _ _ x₁ x₂
--valuesDoNotStep .true t' () V-True
--valuesDoNotStep .false t' () V-False
--valuesDoNotStep .zero t' () V-Zero
--valuesDoNotStep step t (E-Succ step) (V-Succ v) = valuesDoNotStep _ _ step v


-- A term is reducible when some evaluation step can be applied to it.
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : {t' : Term ty} -> Step t t' -> Red t

-- A term is considered a normal form whenever it is not reducible.
NF : ∀ {ty} -> Term ty → Set
NF t = Red t -> Empty

toVal : forall {ty} -> (t : Term ty) -> IsValue t -> Value ty
toVal .true V-True = vtrue
toVal .false V-False = vfalse
toVal .zero V-Zero = vnat Zero
toVal ._ (V-Succ x₁) with toVal _ x₁
toVal ._ (V-Succ x₁) | vnat x₂ = vnat (Succ x₂)
--toVal .true V-True = vtrue
--toVal .false V-False = vfalse
--toVal .zero V-Zero = vnat Zero
--toVal _ (V-Succ v) with toVal _ v
--toVal _ (V-Succ v) | vnat x₁ = vnat (Succ x₁)

mutual
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
  if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t1) t2 t3 with iszero-reduces t1
  if-reduces (iszero t1) t2 t3 | Reduces x = Reduces (E-If-If x)

  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂ 
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x = Reduces (E-IsZeroSucc (normal-forms-are-values _ x))
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))

  succ-nf : (k : Term NAT) -> NF (succ k) -> Red k -> Empty
  succ-nf _ nf (Reduces x) = nf (Reduces (E-Succ x))

  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → IsValue t
  normal-forms-are-values true nf = V-True
  normal-forms-are-values false nf = V-False
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf = V-Zero
  normal-forms-are-values (succ t) nf = V-Succ (normal-forms-are-values t (succ-nf t nf))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))

  values-are-normal-forms : forall {ty} -> {t : Term ty} -> IsValue t -> NF t
  values-are-normal-forms p (Reduces step) = valuesDoNotStep _ _ step p

  lemma : (k : Term NAT) -> NF k -> NF (succ k)
  lemma t nf (Reduces (E-Succ x)) = nf (Reduces x)

  progress : {ty : Type} -> (t : Term ty) -> Either (NF t) (Red t)
  progress true = Left (values-are-normal-forms V-True)
  progress false = Left (values-are-normal-forms V-False)
  progress (if t then t₁ else t₂) = Right (if-reduces _ _ _)
  progress zero = Left (values-are-normal-forms V-Zero)
  progress (succ t) with progress t
  progress (succ t) | Left x = Left (lemma t x)
  progress (succ t) | Right (Reduces step) = Right (Reduces (E-Succ step))
  progress (iszero t) = Right (iszero-reduces _ )

--------------------------------------------------------------------------------
---------------------------       EXERCISES       ------------------------------
--------------------------------------------------------------------------------


-- Prove that the small step semantics is deterministic
deterministic : ∀ {ty} (t t₁ t₂ : Term ty) → Step t t₁ → Step t t₂ → t₁ == t₂
deterministic ._ t₁ .t₁ E-If-True E-If-True = refl
deterministic ._ t₁ ._ E-If-True (E-If-If ())
deterministic ._ t₁ .t₁ E-If-False E-If-False = refl
deterministic ._ t₁ ._ E-If-False (E-If-If ())
deterministic ._ ._ t₂ (E-If-If ()) E-If-True
deterministic ._ ._ t3 (E-If-If ()) E-If-False
deterministic ._ ._ ._ (E-If-If step₁) (E-If-If step₂)  with deterministic _ _ _ step₁ step₂ 
deterministic ._ ._ ._ (E-If-If step₁) (E-If-If step₂) | refl = refl
deterministic ._ ._ ._ (E-Succ step₁) (E-Succ step₂) with deterministic _ _ _ step₁ step₂
deterministic ._ ._ ._ (E-Succ step₁) (E-Succ step₂) | refl = refl
deterministic .(iszero zero) .true .true E-IsZeroZero E-IsZeroZero = refl
deterministic .(iszero zero) .true ._ E-IsZeroZero (E-IsZero ())
deterministic ._ .false .false (E-IsZeroSucc x) (E-IsZeroSucc x₁) = refl
deterministic .(iszero (succ zero)) .false ._ (E-IsZeroSucc V-Zero) (E-IsZero (E-Succ ()))
deterministic ._ .false ._ (E-IsZeroSucc (V-Succ x₁)) (E-IsZero (E-Succ step₂)) = contradiction (valuesDoNotStep _ _ step₂ (V-Succ x₁))
deterministic .(iszero zero) ._ .true (E-IsZero ()) E-IsZeroZero
deterministic .(iszero (succ zero)) ._ .false (E-IsZero (E-Succ ())) (E-IsZeroSucc V-Zero)
deterministic ._ ._ .false (E-IsZero (E-Succ step₁)) (E-IsZeroSucc (V-Succ x₁)) = contradiction (valuesDoNotStep _ _ step₁ (V-Succ x₁))
deterministic ._ ._ ._ (E-IsZero step₁) (E-IsZero step₂) with deterministic _ _ _ step₁ step₂
deterministic ._ ._ ._ (E-IsZero step₁) (E-IsZero step₂) | refl = refl

-- A sequence of steps that can be applied in succession.
data Steps {ty : Type} : Term ty → Term ty → Set where
  Nil : forall {t} -> Steps t t
  Cons : forall {t1 t2 t3} -> Step t1 t2 -> Steps t2 t3 -> Steps t1 t3

-- Single-step sequence.
[_] : ∀ {ty} {t₁ t₂ : Term ty} -> Step t₁ t₂ -> Steps t₁ t₂
[_] x = Cons x Nil
  
-- Concatenation.
_++_ : ∀ {ty} {t₁ t₂ t₃ : Term ty} → Steps t₁ t₂ → Steps t₂ t₃ → Steps t₁ t₃
Nil ++ stps' = stps'
Cons x stps ++ stps' = Cons x (stps ++ stps')

infixr 5 _++_

--deterministic : ∀ {ty} (t t₁ t₂ : Term ty) → Step t t₁ → Step t t₂ → t₁ == t₂
-- Use the the deterministic property of the small step semantics to
-- show that normal forms are unique
uniqueness-of-normal-forms :
  ∀ {ty} (t t₁ t₂ : Term ty) →
  Steps t t₁ → Steps t t₂ → NF t₁ → NF t₂ → t₁ == t₂
uniqueness-of-normal-forms t .t .t Nil Nil x x₁ = refl
uniqueness-of-normal-forms t .t t₂ Nil (Cons x step₂) nf₁ nf₂ = contradiction (nf₁ (Reduces x))
uniqueness-of-normal-forms t t₁ .t (Cons x step₁) Nil nf₁ nf₂ = contradiction (nf₂ (Reduces x))
uniqueness-of-normal-forms t t₁ t₂ (Cons x step₁) (Cons x₁ step₂) nf1 nf2 with deterministic _ _ _ x x₁
uniqueness-of-normal-forms t t₁ t₂ (Cons x step₁) (Cons x₁ step₂) nf1 nf2 | refl = uniqueness-of-normal-forms _ t₁ t₂ step₁ step₂ nf1 nf2

------------------------------------------------------------------------
-- Big-step semantics

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  B-Zero : zero ⇓ vnat Zero
  B-True : true ⇓ vtrue
  B-False : false ⇓ vfalse
  B-Succ : ∀ {t : Term NAT} {v : Nat} → t ⇓ vnat v → succ t ⇓ vnat (Succ v)
  B-IfTrue : ∀ {t₁ t₂ t₃ : Term BOOL} {v₁ v₂ v₃ : Value _ } → t₁ ⇓ vtrue → t₂ ⇓ v₂ → (if t₁ then t₂ else t₃) ⇓ v₂  
  B-IfFalse :  ∀ {t₁ t₂ t₃ : Term BOOL} {v₁ v₂ v₃ : Value _ } → t₁ ⇓ vfalse → t₃ ⇓ v₃ → (if t₁ then t₂ else t₃) ⇓ v₃
  B-IsZeroZero : {t₁ : Term NAT} → t₁ ⇓ vnat Zero → iszero t₁ ⇓ vtrue 
  B-IsZeroSucc : {t : Term NAT} {v : Nat} → t ⇓ vnat (Succ v) → iszero t ⇓ vfalse

-- Show how to convert from big step to small step semantics
succStep : ∀ {t₁ t₂ : Term NAT} → Steps t₁ t₂ → Steps (succ t₁) (succ t₂)
succStep Nil = Nil
succStep (Cons x xs) = Cons (E-Succ x) (succStep xs)

isZeroStep : ∀ {t₁ t₂ : Term NAT} → Steps t₁ t₂ → Steps (iszero t₁) (iszero t₂)
isZeroStep Nil = Nil
isZeroStep (Cons x xs) = Cons (E-IsZero x) (isZeroStep xs)



ifStep : ∀ {ty} {t t'} {t₁ t₂ : Term ty} → Steps t t' → Steps (if t then t₁ else t₂) (if t' then t₁ else t₂)
ifStep Nil = Nil
ifStep (Cons x xs) = Cons (E-If-If x) (ifStep xs)

big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small B-Zero = Nil
big-to-small B-True = Nil
big-to-small B-False = Nil
big-to-small (B-Succ x) = succStep (big-to-small x)
big-to-small (B-IfTrue x x₁) = (ifStep (big-to-small x)) ++ Cons E-If-True (big-to-small x₁)
big-to-small (B-IfFalse x x₁) = (ifStep (big-to-small x)) ++ Cons E-If-False (big-to-small x₁)
big-to-small (B-IsZeroZero x) = isZeroStep (big-to-small x) ++ Cons E-IsZeroZero Nil
big-to-small (B-IsZeroSucc x) = (isZeroStep (big-to-small x)) ++ Cons (E-IsZeroSucc {!!}) Nil

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (t : Term ty) -> (p : IsValue t) -> t ⇓ toVal t p
value-to-value .true V-True = B-True
value-to-value .false V-False = B-False
value-to-value .zero V-Zero = B-Zero
value-to-value ._ (V-Succ p) = {!B-Succ!}


-- And conversion in the other direction
small-to-big : {ty : Type} -> (t t' : Term ty) -> (p : IsValue t') → Steps t t' → t ⇓ toVal t' p
small-to-big t v steps = λ x → {!!}
  where
  prepend-step : {ty : Type} -> (t t' : Term ty) (v : Value ty) → Step t t' -> t' ⇓ v → t ⇓ v
  prepend-step ._ .zero .(vnat Zero) E-If-True B-Zero = {!!}
  prepend-step ._ .true .vtrue E-If-True B-True = {!!}
  prepend-step ._ .false .vfalse E-If-True B-False = {!!}
  prepend-step ._ ._ ._ E-If-True (B-Succ step₂) = {!!}
  prepend-step ._ ._ v₁ E-If-True (B-IfTrue step₂ step₃) = {!!}
  prepend-step ._ ._ v₁ E-If-True (B-IfFalse step₂ step₃) = {!!}
  prepend-step ._ ._ .vtrue E-If-True (B-IsZeroZero step₂) = {!!}
  prepend-step ._ ._ .vfalse E-If-True (B-IsZeroSucc step₂) = {!!}
  prepend-step ._ .zero .(vnat Zero) E-If-False B-Zero = {!!}
  prepend-step ._ .true .vtrue E-If-False B-True = {!!}
  prepend-step ._ .false .vfalse E-If-False B-False = {!!}
  prepend-step ._ ._ ._ E-If-False (B-Succ step₂) = {!!}
  prepend-step ._ ._ v₁ E-If-False (B-IfTrue step₂ step₃) = {!!}
  prepend-step ._ ._ v₁ E-If-False (B-IfFalse step₂ step₃) = {!!}
  prepend-step ._ ._ .vtrue E-If-False (B-IsZeroZero step₂) = {!!}
  prepend-step ._ ._ .vfalse E-If-False (B-IsZeroSucc step₂) = {!!}
  prepend-step ._ ._ v₁ (E-If-If step₁) (B-IfTrue step₂ step₃) = {!!}
  prepend-step ._ ._ v₁ (E-If-If step₁) (B-IfFalse step₂ step₃) = {!!}
  prepend-step ._ ._ ._ (E-Succ step₁) (B-Succ step₂) = {!!}
  prepend-step .(iszero zero) .true .vtrue E-IsZeroZero B-True = {!!}
  prepend-step ._ .false .vfalse (E-IsZeroSucc x) B-False = {!!}
  prepend-step ._ ._ .vtrue (E-IsZero step₁) (B-IsZeroZero step₂) = {!!}
  prepend-step ._ ._ .vfalse (E-IsZero step₁) (B-IsZeroSucc step₂) = {!!}

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = B-True
⇓-complete false = B-False
⇓-complete (if t then t₁ else t₂) = {!!}
⇓-complete zero = B-Zero
⇓-complete (succ t) = {!!}
⇓-complete (iszero t) = {!!}

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound t v x = {!!}

