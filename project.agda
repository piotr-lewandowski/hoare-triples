module project where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _+_; _*_) renaming (_≡ᵇ_ to _==_; _∸_ to _-_; _<ᵇ_ to _<_; _≤ᵇ_ to _≤_)
open Eq using (_≡_; refl; cong)
open import Data.Bool.Base using (T)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

-- Environment
data Assignment (A : Set) : Set where
  _:=_ : A → ℕ → Assignment A

data MemoryState (A : Set) : Set where
  empty : MemoryState A
  _v_ : Assignment A → MemoryState A → MemoryState A

infixr 5 _v_

record ProgramState : Set where
    field
        variables : MemoryState String
        heap : MemoryState ℕ
open ProgramState public

-- Syntax
data Expr : Set where
  Num : ℕ → Expr
  Var : String → Expr
  Add : Expr → Expr → Expr
  Sub : Expr → Expr → Expr
  Mul : Expr → Expr → Expr
  Deref : Expr → Expr

data BoolExpr : Set where
  Eq : Expr → Expr → BoolExpr
  Lt : Expr → Expr → BoolExpr

data Assertion : Set₁ where
    assertion : (p : ProgramState → Set) → Assertion

data Isempty : ProgramState → Set where
  isempty : Isempty record { variables = empty; heap = empty }

test : Assertion
test = assertion λ p → Isempty p

data Command : Set₁ where
  Skip : Command
  Assign : String → Expr → Command
  AssignDeref : Expr → Expr → Command
  Seq : Command → Command → Command
  If : BoolExpr → Command → Command → Command
  While : Assertion → BoolExpr → Command → Command
  Assert : Assertion → Command

-- Semantics
initialState : ProgramState
initialState = record { variables = empty; heap = empty }

data _contains_ { A } : MemoryState A → Assignment A → Set where
  top : ∀ { a : Assignment A } → ∀ { c : MemoryState A }
    →  (a v c) contains a
  tail : ∀ { x y } → ∀ { m n } → ∀ { c : MemoryState A }
    → ( c contains ( x := n ) )
    → ¬ ( x ≡ y ) -- dodatkowo zakładamy, że jeśli sprawdzamy, czy zmienna jest dalej w ciągu, to upewniamy się,
                  -- że nie jest na pierwszej pozycji
    → ( (y := m) v c ) contains (x := n)


-- to może mogłoby korzystać z porównania w bibliotece standardowej
-- equality on naturals
sucEq : ∀ {x y : ℕ} → suc x ≡ suc y → x ≡ y
sucEq refl = refl

inequalityCong : ∀ {x y : ℕ} → ¬ x ≡ y → ¬ (suc x ≡ suc y)
inequalityCong ¬x≡y x+1≡y+1 = ¬x≡y (sucEq x+1≡y+1)

_=ₙ_ : ∀ ( x y : ℕ ) → Dec ( x ≡ y )
zero =ₙ zero = yes refl
zero =ₙ (suc y) = no (λ ())
(suc x) =ₙ zero = no (λ ())
(suc x) =ₙ (suc y) with x =ₙ y
... | yes p = yes (cong suc p)
... | no ¬p = no (inequalityCong ¬p)

retrieve : ℕ → MemoryState ℕ → ℕ
retrieve _ empty = 0
retrieve x (y := w v c) with x =ₙ y
... | yes _ = w
... | no _ = retrieve x c

retrieveString : String → MemoryState String → ℕ
retrieveString _ empty = 0
retrieveString x (y := w v c) = {!   !}

evalExpr : ProgramState → Expr → ℕ
evalExpr p (Num n) = n
evalExpr p (Var x) = retrieveString x (variables p)
evalExpr p (Add e1 e2) = evalExpr p e1 + evalExpr p e2
evalExpr p (Sub e1 e2) = evalExpr p e1 - evalExpr p e2
evalExpr p (Mul e1 e2) = evalExpr p e1 * evalExpr p e2
evalExpr p (Deref e) = retrieve (evalExpr p e) (heap p)

evalBoolExpr : ProgramState → BoolExpr → Bool
evalBoolExpr p (Eq e1 e2) = evalExpr p e1 == evalExpr p e2
evalBoolExpr p (Lt e1 e2) = evalExpr p e1 < evalExpr p e2

_withH_ : ProgramState → Assignment ℕ → ProgramState
p withH a = record p { heap = a v heap p }

_withV_ : ProgramState → Assignment String → ProgramState
p withV a = record p { variables = a v variables p }

data BigStep : ProgramState → Command → ProgramState → Set₁ where
    sSkip : ∀ { p : ProgramState } → BigStep p Skip p
    sAssign : ∀ { p : ProgramState} → { x : String } → { e : Expr } 
        → BigStep p (Assign x e) (p withV (x := evalExpr p e))
    sAssignDeref : ∀ { p : ProgramState} → { e1 : Expr } → { e2 : Expr }
        → BigStep p (AssignDeref e1 e2) (p withH (evalExpr p e1 := evalExpr p e2))
    sSeq : ∀ { p p' p'' : ProgramState } → { c1 c2 : Command }
        → BigStep p c1 p' → BigStep p' c2 p'' → BigStep p (Seq c1 c2) p''
    sIfTrue : ∀ { p p' : ProgramState } → { b : BoolExpr } → { c1 c2 : Command }
        → evalBoolExpr p b ≡ true → BigStep p c1 p' → BigStep p (If b c1 c2) p'
    sIfFalse : ∀ { p p' : ProgramState } → { b : BoolExpr } → { c1 c2 : Command }
        → evalBoolExpr p b ≡ false → BigStep p c2 p' → BigStep p (If b c1 c2) p'
    sWhileTrue : ∀ { p p' p'' : ProgramState } → ∀ { x : Assertion } → { b : BoolExpr } → { c : Command }
        → evalBoolExpr p b ≡ true → BigStep p c p' → BigStep p' (While x b c) p'' → BigStep p (While x b c) p''
    sWhileFalse : ∀ { p : ProgramState } → ∀ { x : Assertion } → { b : BoolExpr } → { c : Command }
        → evalBoolExpr p b ≡ false → BigStep p (While x b c) p
    sAssert : ∀ { p : ProgramState } → ∀ { x }
        → x p
        → BigStep p (Assert (assertion x)) p

data HoareTriple : Assertion → Command → Assertion → Set₁ where
    hSkip : ∀ { x : Assertion } → HoareTriple x Skip x
    --   hoare_triple P (Assign x e) (fun h v => exists v', P h v' /\ v = v' $+ (x, eval e h v'))
    -- hAssign : ∀ { P } → { e : Expr } → { x : String }
    --     → HoareTriple (assertion P) (Assign x e) (assertion (λ p → ∃ v' (P (record p { variables = v' } ) ∧ v' ≡ variables (p withV (x := e) ))))
    -- hAssignDeref : ∀ { x y } → { e1 e2 : Expr }
    --     → (∀ { p : ProgramState } → x p → y (p withH (evalExpr p e1 := evalExpr p e2))) → HoareTriple (assertion x) (AssignDeref e1 e2) (assertion y)
    hAssert : ∀ { x y } → { c : Command }
        → (∀ { p : ProgramState } → x p → y p) 
        → HoareTriple (assertion x) (Assert (assertion y)) (assertion x)
    hConsequence : ∀ { x1 x2 y1 y2 } → { c : Command }
        → HoareTriple (assertion x1) c (assertion y1) 
        → (∀ { p : ProgramState } → x2 p → x1 p) 
        → (∀ { p : ProgramState } → y1 p → y2 p ) 
        → HoareTriple (assertion x2) c (assertion y2)

soundness : ∀ { P c Q } 
    → HoareTriple (assertion P) c (assertion Q) 
    → ∀ { p p' } 
    → BigStep p c p' 
    → P p 
    → Q p'
soundness = {!!}