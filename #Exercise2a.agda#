--Studentnr: 5597250
--Matthew Swat
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
  TUPLE : Type → Type → Type


-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : forall {σ} -> (c : Term BOOL) -> (t e : Term σ) → Term σ
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero       : (n : Term NAT) -> Term BOOL
  （_,_）       : ∀ {l r}  → Term l → Term r →  Term (TUPLE l r) 
  fst             :  ∀ {l r}  → Term (TUPLE l r) → Term l
  snd             :  ∀ {l r} → Term (TUPLE l r) → Term r

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And what else?
  vnat : Nat -> Value NAT
  （_,_） : ∀{l r} → Value l → Value r →  Value (TUPLE l r)


-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat Zero ⌝ = zero
⌜ vnat (Succ x) ⌝ = succ ⌜ vnat x ⌝ 
⌜ （ l , r ） ⌝ = （ ⌜ l ⌝ , ⌜ r ⌝ ）

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
⟦ （ l , r ） ⟧ = （ ⟦ l ⟧ , ⟦ r ⟧ ）
⟦ fst x ⟧  with ⟦ x ⟧
⟦ fst x ⟧ | （ l , r ） = l
⟦ snd x ⟧ with ⟦ x ⟧ 
⟦ snd x ⟧ | （ l , r ） = r

-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data IsValue : {ty : Type} -> Term ty -> Set where
  V-True : IsValue true
  V-False : IsValue false
  V-Zero : IsValue zero
  V-Succ : ∀ {x} -> IsValue x -> IsValue (succ x)
  V-Tuple : ∀ {ty ty' l r} → IsValue {ty} l → IsValue {ty'} r → IsValue （ l , r ）


isValueComplete : forall {ty} -> (v : Value ty) -> IsValue ⌜ v ⌝ 
isValueComplete vtrue = V-True
isValueComplete vfalse = V-False
isValueComplete (vnat Zero) = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))
isValueComplete （ l , r ） = V-Tuple (isValueComplete l) (isValueComplete r)

isValueSound : forall {ty} {t : Term ty} -> IsValue t -> Exists (Value ty) (\v -> ⌜ v ⌝ == t)
isValueSound V-True = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero = Witness (vnat Zero) refl
isValueSound (V-Succ p) with isValueSound p
isValueSound (V-Succ p) | Witness (vnat k) q = Witness (vnat (Succ k) ) (cong succ q)
isValueSound (V-Tuple l r) with isValueSound l | isValueSound r
isValueSound (V-Tuple l r) | Witness l₁ refl | Witness r₁ refl = Witness （ l₁ , r₁ ） refl


data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ : forall {t t' : Term NAT} -> Step t t' -> Step (succ t) (succ t') 
  E-IsZeroZero : Step (iszero zero) true
  E-IsZeroSucc : ∀ {t : Term NAT} -> IsValue t -> Step (iszero (succ t)) false
  E-IsZero : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
 
  E-EvalFst : ∀ {tyL tyR} {l l' : Term tyL} {r : Term tyR}  → Step l l'  → Step （ l , r ） （ l' , r ）
  E-EvalSnd : ∀ {tyL tyR} {r r' : Term tyR} {l : Term tyL}  → Step r r'  → Step （ l , r ） （ l , r' ）
  E-ProjFst :  ∀ {l r}  {t t' : Term (TUPLE l r)}  → Step t t' → Step (fst t) (fst t')
  E-ProjFst' : ∀ {tyL tyR} {l : Term tyL} {r : Term tyR} → Step (fst （ l , r ）) l
  E-ProjSnd :  ∀ {l r}  → {t t' : Term (TUPLE l r)}  → Step t t' → Step (snd t) (snd t')
  E-ProjSnd' :  ∀  {tyL tyR} {l : Term tyL} {r : Term tyR} → Step (snd （ l , r ）) r
 
preservation : ∀ {ty} -> (t t' : Term ty) -> Step t t' -> ty == ty
preservation t t' step = refl

valuesDoNotStep : forall {ty} -> (t t' : Term ty) -> Step t t' -> IsValue t -> Empty
valuesDoNotStep .true t' () V-True
valuesDoNotStep .false t' () V-False
valuesDoNotStep .zero t' () V-Zero
valuesDoNotStep ._ ._ (E-Succ x₁) (V-Succ x₂) = valuesDoNotStep _ _ x₁ x₂
valuesDoNotStep ._ ._ (E-EvalFst y) (V-Tuple z z₁) = valuesDoNotStep _ _ y z
valuesDoNotStep ._ ._ (E-EvalSnd y) (V-Tuple z z₁) = valuesDoNotStep _ _ y z₁
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
toVal ._ (V-Tuple l r) = （ toVal _ l , toVal _ r ）
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
  if-reduces (fst x) y z with fst-reduces x
  if-reduces (fst x) y z | Reduces x₁ = Reduces (E-If-If x₁)
  if-reduces (snd x) y z with snd-reduces x
  if-reduces (snd x) y z | Reduces x₁ = Reduces (E-If-If x₁)

  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂ 
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x = Reduces (E-IsZeroSucc (normal-forms-are-values _ x))
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (fst x) with fst-reduces x
  iszero-reduces (fst x) | Reduces x₁ = Reduces (E-IsZero x₁)
  iszero-reduces (snd x) with snd-reduces x
  iszero-reduces (snd x) | Reduces x₁ = Reduces (E-IsZero x₁) 

  fst-reduces : ∀ {l r} → (t : Term (TUPLE l r)) -> Red (fst t) 
  fst-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  fst-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-ProjFst x)
  fst-reduces （ t , t₁ ） = Reduces E-ProjFst'
  fst-reduces (fst t) with fst-reduces t
  fst-reduces (fst t) | Reduces x = Reduces (E-ProjFst x)
  fst-reduces (snd t) with fst-reduces t
  fst-reduces (snd ._) | Reduces E-ProjFst' = Reduces (E-ProjFst E-ProjSnd')
  fst-reduces (snd t) | Reduces (E-ProjFst x) = Reduces (E-ProjFst (E-ProjSnd x))

  snd-reduces : ∀ {l r} → (t : Term (TUPLE l r)) -> Red (snd t) 
  snd-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  snd-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-ProjSnd x)
  snd-reduces （ t , t₁ ） = Reduces E-ProjSnd'
  snd-reduces (fst t) with fst-reduces t
  snd-reduces (fst t) | Reduces x = Reduces (E-ProjSnd x)
  snd-reduces (snd t) with snd-reduces t
  snd-reduces (snd t) | Reduces x = Reduces (E-ProjSnd x)

  succ-nf : (k : Term NAT) -> NF (succ k) -> Red k -> Empty
  succ-nf _ nf (Reduces x) = nf (Reduces (E-Succ x))


  fst-nf : ∀ {tyL tyR} (l : Term tyL) → (r : Term tyR) → NF （ l , r ）  → NF l 
  fst-nf l r nf (Reduces x₁) = nf (Reduces (E-EvalFst x₁))


  snd-nf : ∀ {tyL tyR} (l : Term tyL) → (r : Term tyR) → NF （ l , r ）  → NF r 
  snd-nf l r nf (Reduces x₁) = nf (Reduces (E-EvalSnd x₁))

  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → IsValue t
  normal-forms-are-values true nf = V-True
  normal-forms-are-values false nf = V-False
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf = V-Zero
  normal-forms-are-values (succ t) nf = V-Succ (normal-forms-are-values t (succ-nf t nf))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))
  normal-forms-are-values （ l , r ） nf  = V-Tuple (normal-forms-are-values l (fst-nf l r nf)) (normal-forms-are-values r (snd-nf l r nf))
  normal-forms-are-values (fst t) nf = contradiction (nf (fst-reduces t))
  normal-forms-are-values (snd t) nf = contradiction (nf (snd-reduces t))
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
  progress （ l , r ） with progress l | progress r
  progress （ l₁ , r₁ ） | l₂ | Left x = Left {!!}
  progress （ l₁ , r₁ ） | l₂ | Right x = Right {!!}
  progress (fst x) = Right (fst-reduces x)
  progress (snd x) = Right (snd-reduces x)

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
deterministic ._ ._ ._ (E-EvalFst y) (E-EvalFst z) with deterministic _ _ _ y z
deterministic ._ ._ ._ (E-EvalFst y) (E-EvalFst z) | refl = refl
deterministic ._ ._ ._ (E-EvalFst y) (E-EvalSnd z) = contradiction (valuesDoNotStep _ _ y {!!})
deterministic ._ ._ ._ (E-EvalSnd y) (E-EvalFst z) = contradiction (valuesDoNotStep _ _ y {!!})
deterministic ._ ._ ._ (E-EvalSnd y) (E-EvalSnd z) with deterministic _ _ _ y z
deterministic ._ ._ ._ (E-EvalSnd y) (E-EvalSnd z) | refl = refl
deterministic ._ t₃ .t₃ E-ProjFst' E-ProjFst' = refl
deterministic ._ t₂ ._ E-ProjFst' (E-ProjFst z) = contradiction (valuesDoNotStep _ _ z {!!})
deterministic ._ t₃ .t₃ E-ProjSnd' E-ProjSnd' = refl
deterministic ._ t₂ ._ E-ProjSnd' (E-ProjSnd z) = contradiction (valuesDoNotStep _ _ z {!!})
deterministic ._ ._ t₃ (E-ProjFst y) E-ProjFst' = contradiction (valuesDoNotStep _ _ y {!!})
deterministic ._ ._ ._ (E-ProjFst y) (E-ProjFst z) = cong fst (deterministic _ _ _ y z) 
deterministic ._ ._ t₃ (E-ProjSnd y) E-ProjSnd' = {!!}
deterministic ._ ._ ._ (E-ProjSnd y) (E-ProjSnd z) = cong snd (deterministic _ _ _ y z)

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
  B-Succ : ∀ {nv n}  → n ⇓ vnat nv → succ n ⇓ vnat (Succ nv)
  B-IfTrue : {ty : Type} {t₂ t₃ : Term ty} → ∀ {t₁ v} → t₁ ⇓ vtrue → t₂ ⇓ v → if t₁ then t₂ else t₃ ⇓ v
  B-IfFalse :  {ty : Type} {t₂ t₃ : Term ty} → ∀ {t₁ v} → t₁ ⇓ vfalse → t₃ ⇓ v → if t₁ then t₂ else t₃ ⇓ v
  B-IsZeroZero : ∀ {t₁} → t₁ ⇓ vnat Zero → iszero t₁ ⇓ vtrue 
  B-IsZeroSucc : ∀ {nv t} →  t ⇓ vnat (Succ nv)  → iszero  t ⇓ vfalse
  B-EvalTuple : ∀ {tyL tyR lv rv} {l : Term tyL} {r : Term tyR} →  l ⇓ lv  → r ⇓ rv  → （ l , r ） ⇓ （ lv , rv ）
  B-ProjFst : ∀ {l r} {t : Term (TUPLE l r)} {lv : Value  l} {rv : Value r}   → t ⇓ （ lv , rv ） → fst t ⇓ lv
  B-ProjSnd : ∀ {l r} {t : Term (TUPLE l r)} {lv : Value  l} {rv : Value r}   → t ⇓ （ lv , rv ） → snd t ⇓ rv



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


fstStep : ∀ {l r}  {t t' : Term (TUPLE l r)}  → Steps t t' → Steps (fst t) (fst t')
fstStep Nil = Nil
fstStep (Cons x x₁) = Cons (E-ProjFst x) (fstStep x₁)

sndStep : ∀ {l r}  {t t' : Term (TUPLE l r)}  → Steps t t' → Steps (snd t) (snd t')
sndStep Nil = Nil
sndStep (Cons x x₁) = Cons (E-ProjSnd x) (sndStep x₁)

tupleFstStep  : ∀ {tyL tyR} {l l' : Term tyL} {r : Term tyR}  → Steps l l'  → Steps （ l , r ） （ l' , r ）
tupleFstStep Nil = Nil
tupleFstStep (Cons x x₁) = Cons (E-EvalFst x) (tupleFstStep x₁)

tupleSndStep  : ∀ {tyL tyR} {l  : Term tyL} {r r' : Term tyR}  → Steps r r'  → Steps （ l , r ） （ l , r' ）
tupleSndStep Nil = Nil
tupleSndStep (Cons x x₁) = Cons (E-EvalSnd x) (tupleSndStep x₁)


big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small B-Zero = Nil
big-to-small B-True = Nil
big-to-small B-False = Nil
big-to-small (B-Succ x) = succStep (big-to-small x)
big-to-small (B-IfTrue x x₁) = (ifStep (big-to-small x)) ++ Cons E-If-True (big-to-small x₁)
big-to-small (B-IfFalse x x₁) = (ifStep (big-to-small x)) ++ Cons E-If-False (big-to-small x₁)
big-to-small (B-IsZeroZero x) = isZeroStep (big-to-small x) ++ Cons E-IsZeroZero Nil
big-to-small (B-IsZeroSucc {a} {b} x) = isZeroStep (big-to-small x) ++ Cons (E-IsZeroSucc {!!}) Nil
big-to-small (B-EvalTuple l r) = tupleFstStep (big-to-small l) ++ tupleSndStep (big-to-small r)
big-to-small (B-ProjFst x) = fstStep (big-to-small x) ++ Cons E-ProjFst' Nil
big-to-small (B-ProjSnd x) = sndStep (big-to-small x) ++ Cons E-ProjSnd' Nil


-- Conversion from small- to big-step representations.

succLemma :  (x : Term NAT) →  (p : IsValue x)  → toVal x p == ⟦ x ⟧  → succ x ⇓ toVal (succ x) (V-Succ p)
succLemma .zero V-Zero refl = B-Succ B-Zero
succLemma (succ p') (V-Succ p) x₁ = {!!}

value-to-value : forall {ty} (t : Term ty) -> (p : IsValue t) -> t ⇓ toVal t p
value-to-value true V-True = B-True
value-to-value false V-False = B-False
value-to-value zero V-Zero = B-Zero
value-to-value (succ x) (V-Succ p) = succLemma x p {!!}
value-to-value （ l , r ） (V-Tuple l₁ r₁) = B-EvalTuple (value-to-value l l₁) (value-to-value r r₁)

prepend-step : {ty : Type} -> (t t' : Term ty) (v : Value ty) → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step ._ .zero .(vnat Zero) E-If-True B-Zero = B-IfTrue B-True B-Zero
prepend-step ._ .zero .(vnat Zero) E-If-False B-Zero = B-IfFalse B-False B-Zero
prepend-step ._ .true .vtrue E-If-True B-True = B-IfTrue B-True B-True
prepend-step ._ .true .vtrue E-If-False B-True = B-IfFalse B-False B-True
prepend-step .(iszero zero) .true .vtrue E-IsZeroZero B-True = B-IsZeroZero B-Zero
prepend-step ._ .false .vfalse E-If-True B-False = B-IfTrue B-True B-False
prepend-step ._ .false .vfalse E-If-False B-False = B-IfFalse B-False B-False
prepend-step ._ .false .vfalse (E-IsZeroSucc x₁) B-False = {!!}
prepend-step ._ ._ ._ E-If-True (B-Succ x₂) = B-IfTrue B-True (B-Succ x₂)
prepend-step ._ ._ ._ E-If-False (B-Succ x₂) = B-IfFalse B-False (B-Succ x₂)
prepend-step ._ ._ ._ (E-Succ x₁) (B-Succ x₂) = B-Succ (prepend-step _ _ (vnat _) x₁ x₂)
prepend-step ._ ._ v₁ E-If-True (B-IfTrue x₂ x₃) = B-IfTrue B-True (B-IfTrue x₂ x₃)
prepend-step ._ ._ v₁ E-If-False (B-IfTrue x₂ x₃) = B-IfFalse B-False (B-IfTrue x₂ x₃)
prepend-step ._ ._ v₁ (E-If-If x₁) (B-IfTrue x₂ x₃) = B-IfTrue (prepend-step _ _ vtrue x₁ x₂) x₃
prepend-step ._ ._ v₁ E-If-True (B-IfFalse x₂ x₃) = B-IfTrue B-True (B-IfFalse x₂ x₃)
prepend-step ._ ._ v₁ E-If-False (B-IfFalse x₂ x₃) = B-IfFalse B-False (B-IfFalse x₂ x₃)
prepend-step ._ ._ v₁ (E-If-If x₁) (B-IfFalse x₂ x₃) = B-IfFalse (prepend-step _ _ vfalse x₁ x₂) x₃
prepend-step ._ ._ .vtrue E-If-True (B-IsZeroZero x₂) = B-IfTrue B-True (B-IsZeroZero x₂)
prepend-step ._ ._ .vtrue E-If-False (B-IsZeroZero x₂) = B-IfFalse B-False (B-IsZeroZero x₂)
prepend-step ._ ._ .vtrue (E-IsZero x₁) (B-IsZeroZero x₂) = B-IsZeroZero (prepend-step _ _ (vnat Zero) x₁ x₂)
prepend-step ._ ._ .vfalse E-If-True (B-IsZeroSucc x₂) = B-IfTrue B-True (B-IsZeroSucc x₂)
prepend-step ._ ._ .vfalse E-If-False (B-IsZeroSucc x₂) = B-IfFalse B-False (B-IsZeroSucc x₂)
prepend-step ._ ._ .vfalse (E-IsZero x₁) (B-IsZeroSucc x₂) = B-IsZeroSucc (prepend-step _ _ (vnat (Succ _)) x₁ x₂)
prepend-step ._ ._ ._ E-If-True (B-EvalTuple e e₁) = B-IfTrue B-True (B-EvalTuple e e₁)
prepend-step ._ ._ c E-If-True (B-ProjFst e) = B-IfTrue B-True (B-ProjFst e)
prepend-step ._ ._ c E-If-True (B-ProjSnd e) = B-IfTrue B-True (B-ProjSnd e)
prepend-step ._ ._ ._ E-If-False (B-EvalTuple e e₁) = B-IfFalse B-False (B-EvalTuple e e₁)
prepend-step ._ ._ c E-If-False (B-ProjFst e) = B-IfFalse B-False (B-ProjFst e)
prepend-step ._ ._ c E-If-False (B-ProjSnd e) = B-IfFalse B-False (B-ProjSnd e)
prepend-step ._ ._ ._ (E-EvalFst d) (B-EvalTuple e e₁) = B-EvalTuple (prepend-step _ _ _ d e) e₁
prepend-step ._ ._ ._ (E-EvalSnd d) (B-EvalTuple e e₁) = B-EvalTuple e (prepend-step _ _ _ d e₁)
prepend-step ._ ._ z (E-ProjFst a) (B-ProjFst b) = B-ProjFst (prepend-step _ _ （ z , _ ） a b)
prepend-step ._ .zero .(vnat Zero) E-ProjFst' B-Zero = {!!}
prepend-step ._ .true .vtrue E-ProjFst' B-True = {!!}
prepend-step ._ .false .vfalse E-ProjFst' B-False = {!!}
prepend-step ._ ._ ._ E-ProjFst' (B-Succ b) = {!!}
prepend-step ._ ._ z E-ProjFst' (B-IfTrue b b₁) = {!!}
prepend-step ._ ._ z E-ProjFst' (B-IfFalse b b₁) = {!!}
prepend-step ._ ._ .vtrue E-ProjFst' (B-IsZeroZero b) = {!!}
prepend-step ._ ._ .vfalse E-ProjFst' (B-IsZeroSucc b) = {!!}
prepend-step ._ ._ ._ E-ProjFst' (B-EvalTuple b b₁) = {!!}
prepend-step ._ ._ z E-ProjFst' (B-ProjFst b) = {!!}
prepend-step ._ ._ z E-ProjFst' (B-ProjSnd b) = {!!}
prepend-step ._ ._ z (E-ProjSnd a) (B-ProjSnd b) = {!!}
prepend-step ._ .zero .(vnat Zero) E-ProjSnd' B-Zero = {!!}
prepend-step ._ .true .vtrue E-ProjSnd' B-True = {!!}
prepend-step ._ .false .vfalse E-ProjSnd' B-False = {!!}
prepend-step ._ ._ ._ E-ProjSnd' (B-Succ b) = {!!}
prepend-step ._ ._ z E-ProjSnd' (B-IfTrue b b₁) = {!!}
prepend-step ._ ._ z E-ProjSnd' (B-IfFalse b b₁) = {!!}
prepend-step ._ ._ .vtrue E-ProjSnd' (B-IsZeroZero b) = {!!}
prepend-step ._ ._ .vfalse E-ProjSnd' (B-IsZeroSucc b) = {!!}
prepend-step ._ ._ ._ E-ProjSnd' (B-EvalTuple b b₁) = {!!}
prepend-step ._ ._ z E-ProjSnd' (B-ProjFst b) = {!!}
prepend-step ._ ._ z E-ProjSnd' (B-ProjSnd b) = {!!}

-- And conversion in the other direction
small-to-big : {ty : Type} -> (t t' : Term ty) -> (p : IsValue t') → Steps t t' → t ⇓ toVal t' p
small-to-big .true .true V-True Nil = B-True
small-to-big .false .false V-False Nil = B-False
small-to-big .zero .zero V-Zero Nil = B-Zero
small-to-big ._ ._ (V-Succ {x} p) Nil = value-to-value (succ x) (V-Succ p)
small-to-big ._ t' p (Cons E-If-True x₁) = prepend-step _ _ _ E-If-True (small-to-big _ _ p x₁)
small-to-big ._ t' p (Cons E-If-False x₁) = prepend-step _ _  _ E-If-False (small-to-big _ _ p x₁)
small-to-big ._ t' p (Cons (E-If-If x) x₁) = prepend-step _ _ _ (E-If-If x) (small-to-big _ _ p x₁)
small-to-big ._ t' p (Cons (E-Succ x) x₁) = prepend-step _ _ _ (E-Succ x) (small-to-big _ _ p x₁)
small-to-big .(iszero zero) t' p (Cons E-IsZeroZero x₁) = prepend-step _ _ _ E-IsZeroZero (small-to-big _ _ p x₁)
small-to-big ._ t' p (Cons (E-IsZeroSucc x) x₁) = prepend-step _ _ _ (E-IsZeroSucc x) (small-to-big _ _ p x₁)
small-to-big ._ t' p (Cons (E-IsZero x) x₁) = prepend-step _ _ _ (E-IsZero x) (small-to-big _ _ p x₁)
small-to-big ._ ._ (V-Tuple y y₁) Nil =  value-to-value （ _ , _ ） (V-Tuple y y₁)
small-to-big ._ t p (Cons (E-EvalFst x) x₁) = prepend-step _ _ _ (E-EvalFst x) (small-to-big _ _ p x₁)
small-to-big ._ t p (Cons (E-EvalSnd x) x₁) = prepend-step _ _ _ (E-EvalSnd x) (small-to-big _ _ p x₁)
small-to-big ._ t p (Cons E-ProjFst' x) = prepend-step _ _ _ E-ProjFst' (small-to-big _ t p x)
small-to-big ._ t p (Cons E-ProjSnd' x) = prepend-step _ _ _ E-ProjSnd' (small-to-big _ _ p x)
small-to-big ._ t p (Cons (E-ProjFst x) x₁) = prepend-step _ _ _ (E-ProjFst x) (small-to-big _ _ p x₁)
small-to-big ._ t p (Cons (E-ProjSnd x) x₁) = prepend-step _ (snd _) _ (E-ProjSnd x) (small-to-big _ _ p x₁)


--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = B-True
⇓-complete false = B-False
⇓-complete (if t then t₁ else t₂) with ⇓-complete t
... | p with  ⟦ t ⟧
⇓-complete (if t then t₁ else t₂) | w | vtrue = B-IfTrue w (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | w | vfalse = B-IfFalse w (⇓-complete t₂)
⇓-complete zero = B-Zero
⇓-complete (succ t) with ⇓-complete t
... | p with ⟦ t ⟧
⇓-complete (succ t) | p | vnat x = B-Succ p
⇓-complete (iszero t) with ⇓-complete t 
... | p with ⟦ t ⟧
⇓-complete (iszero t) | p₁ | vnat Zero = B-IsZeroZero p₁
⇓-complete (iszero t) | p₁ | vnat (Succ x) = B-IsZeroSucc p₁
⇓-complete (fst x) with ⇓-complete x
... | p with ⟦ x ⟧
⇓-complete (fst x) | p | （ v , v₁ ） = B-ProjFst p
⇓-complete (snd x)  with ⇓-complete x
... | p with ⟦ x ⟧
⇓-complete (snd x) | p | （ v , v₁ ） = B-ProjSnd p 
⇓-complete （ l , r ） = B-EvalTuple (⇓-complete l) (⇓-complete r) 

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound true vtrue x = refl
⇓-sound true vfalse ()
⇓-sound false vtrue ()
⇓-sound false vfalse x = refl
⇓-sound (if t then t₁ else t₂) ty₁ (B-IfTrue x x₁) with  ⟦ t ⟧ | ⇓-sound _ _ x
⇓-sound (if t then t₁ else t₂) ty₁ (B-IfTrue x x₁) | vtrue | refl = ⇓-sound _ _ x₁
⇓-sound (if t then t₁ else t₂) ty₁ (B-IfTrue x x₁) | vfalse | ()
⇓-sound (if t then t₁ else t₂) ty₁ (B-IfFalse x x₁) with ⟦ t ⟧ | ⇓-sound _ _ x
⇓-sound (if t then t₁ else t₂) ty₁ (B-IfFalse x x₁) | vtrue | ()
⇓-sound (if t then t₁ else t₂) ty₁ (B-IfFalse x x₁) | vfalse | refl = ⇓-sound _ _ x₁
⇓-sound zero (vnat Zero) x₁ = refl
⇓-sound zero (vnat (Succ x)) ()
⇓-sound (succ t) (vnat ._) (B-Succ x₁) with ⟦ t ⟧ | ⇓-sound _ _ x₁
⇓-sound (succ t) (vnat .(Succ Zero)) (B-Succ x₁) | vnat Zero | refl = refl
⇓-sound (succ t) (vnat .(Succ (Succ x))) (B-Succ x₁) | vnat (Succ x) | refl = refl
⇓-sound (iszero t) .vtrue (B-IsZeroZero x) with ⟦ t ⟧ | ⇓-sound _ _ x 
⇓-sound (iszero t) .vtrue (B-IsZeroZero x) | .(vnat Zero) | refl = refl
⇓-sound (iszero t) .vfalse (B-IsZeroSucc x) with ⟦ t ⟧ | ⇓-sound _ _ x
⇓-sound (iszero t) .vfalse (B-IsZeroSucc x) | ._ | refl = refl 
⇓-sound （ l , r ） ._ (B-EvalTuple l₁ r₁) with ⟦ l ⟧ | ⇓-sound _ _ l₁ |  ⟦ r ⟧ | ⇓-sound _ _ r₁
⇓-sound （ l₁ , r ） .(（ fl , sr ）) (B-EvalTuple l₂ r₁) | fl | refl | sr | refl = refl 
⇓-sound (fst t) y (B-ProjFst x) with ⟦ t ⟧ | ⇓-sound _ _ x
⇓-sound (fst t) y (B-ProjFst x) | （ .y , rv ） | refl = refl
⇓-sound (snd t) y (B-ProjSnd x) with ⟦ t ⟧ | ⇓-sound _ _ x
⇓-sound (snd t) y (B-ProjSnd x) | （ lv , .y ） | refl = refl
