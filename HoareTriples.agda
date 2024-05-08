module HoareTriples where

-- Basic data types used in the language definition and semantics
open import Data.Nat using (ℕ; _+_; _*_) renaming (_∸_ to _-_; _<ᵇ_ to _<_; _≡ᵇ_ to _≡ₙ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_==_ to _≡ₛ_)

-- Logical operators used mainly in the Hoare triples definition
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (Σ; _×_; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Definition of program state, memory is represented as a list of pairs,
-- either a variable name and it's value or a memory address and it's value
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

-- Abstract definition of language syntax
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

data Command : Set₁ where
  Skip : Command
  Assign : String → Expr → Command
  AssignDeref : Expr → Expr → Command
  Seq : Command → Command → Command
  If : BoolExpr → Command → Command → Command
  While : Assertion → BoolExpr → Command → Command
  Assert : Assertion → Command

-- Helper functions for handling memory, note that if there is no 
-- explicitly set value we simply return 0
retrieveNat : ℕ → MemoryState ℕ → ℕ
retrieveNat _ empty = 0
retrieveNat x (y := w v c) = if x ≡ₙ y 
  then w 
  else retrieveNat x c

retrieveString : String → MemoryState String → ℕ
retrieveString _ empty = 0
retrieveString x (y := w v c) = if x ≡ₛ y 
  then w 
  else retrieveString x c 

initialState : ProgramState
initialState = record { variables = empty; heap = empty }

_withH_ : ProgramState → Assignment ℕ → ProgramState
p withH a = record p { heap = a v heap p }

_withV_ : ProgramState → Assignment String → ProgramState
p withV a = record p { variables = a v variables p }

-- Semantics definition for expressions
evalExpr : ProgramState → Expr → ℕ
evalExpr p (Num n) = n
evalExpr p (Var x) = retrieveString x (variables p)
evalExpr p (Add e1 e2) = evalExpr p e1 + evalExpr p e2
evalExpr p (Sub e1 e2) = evalExpr p e1 - evalExpr p e2
evalExpr p (Mul e1 e2) = evalExpr p e1 * evalExpr p e2
evalExpr p (Deref e) = retrieveNat (evalExpr p e) (heap p)

evalBoolExpr : ProgramState → BoolExpr → Bool
evalBoolExpr p (Eq e1 e2) = evalExpr p e1 ≡ₙ evalExpr p e2
evalBoolExpr p (Lt e1 e2) = evalExpr p e1 < evalExpr p e2

-- Semantics definition for the commands, using big-step semantics
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
        → x p → BigStep p (Assert (assertion x)) p

-- Definition of Hoare triples for all commands
data HoareTriple : Assertion → Command → Assertion → Set₁ where
    hSkip : ∀ { x : Assertion } → HoareTriple x Skip x
    hAssign : ∀ { x } 
        → { e : Expr } 
        → { s : String } 
        → HoareTriple (assertion x) (Assign s e) (assertion (λ p → (∃[ v' ] ((x (record p { variables = v' })) 
        × (variables p ≡ s := (evalExpr (record p { variables = v' }) e) v v')))))
    hAssignDeref : ∀ { x } 
        → { e1 e2 : Expr }
        → HoareTriple (assertion x) (AssignDeref e1 e2) (assertion (λ p → ∃[ h' ] (x (record p { heap = h' })) 
        × (heap p ≡ (evalExpr (record p { heap = h' }) e1) := (evalExpr (record p { heap = h' }) e2) v h')))
    hSeq : ∀ { x y z } 
        → { c1 c2 : Command } 
        → HoareTriple (assertion x) c1 (assertion y)  
        → HoareTriple (assertion y) c2 (assertion z)  
        → HoareTriple (assertion x) (Seq c1 c2) (assertion z)  
    hIf : ∀ { x y z } 
        → { b : BoolExpr } 
        → { c1 c2 : Command } 
        → HoareTriple (assertion (λ p → (x p) × (evalBoolExpr p b ≡ true))) c1 (assertion y) 
        → HoareTriple (assertion (λ p → (x p) × (evalBoolExpr p b ≡ false))) c2 (assertion z) 
        → HoareTriple (assertion x) (If b c1 c2) (assertion (λ p → (y p) ⊎ (z p)))  
    hWhile : ∀ { x y } 
        → { b : BoolExpr } 
        → { c : Command } 
        → (∀ (p : ProgramState) → y p → x p) 
        → HoareTriple (assertion (λ p → (x p) × (evalBoolExpr p b ≡ true))) c (assertion x) 
        → HoareTriple (assertion y) (While (assertion x) b c) (assertion (λ p → (x p) × (evalBoolExpr p b ≡ false)))
    hAssert : ∀ { x y } → { c : Command }
        → (∀ { p : ProgramState } → x p → y p) 
        → HoareTriple (assertion x) (Assert (assertion y)) (assertion x)
    hConsequence : ∀ { x1 x2 y1 y2 } → { c : Command }
        → HoareTriple (assertion x1) c (assertion y1) 
        → (∀ { p : ProgramState } → x2 p → x1 p) 
        → (∀ { p : ProgramState } → y1 p → y2 p ) 
        → HoareTriple (assertion x2) c (assertion y2)

-- Proof of Lemma 14.1 from "Formal Reasoning About Programs" 
lemma : ∀ { x }
    → ∀ { b : BoolExpr } 
    → ∀ { c : Command }
    → (∀ { p p' : ProgramState } → BigStep p c p' → x p → evalBoolExpr p b ≡ true → x p') 
    → (∀ { p p' : ProgramState } → BigStep p (While (assertion x) b c) p' → x p → (x p') × (evalBoolExpr p' b ≡ false))
lemma assumption (sWhileFalse evalBFalse) xp = ⟨ xp , evalBFalse ⟩ 
lemma assumption (sWhileTrue evalBTrue BS1 BS2) xp = lemma assumption BS2 (assumption BS1 xp evalBTrue)

-- Proof of Theorem 14.2 from "Formal Reasoning About Programs"
soundness : ∀ { x y }
    → ∀ { c } 
    → ∀ { p p' } 
    → HoareTriple (assertion x) c (assertion y) 
    → BigStep p c p' 
    → x p 
    → y p' 
soundness hSkip sSkip xp = xp 
soundness {p = p @ record { variables = variables ; heap = heap }} (hAssign {x} {e} {s}) (sAssign {.p} {s} {e}) xp = ⟨ variables , ⟨ xp , refl ⟩  ⟩
soundness {p = p @ record { variables = variables ; heap = heap }} (hAssignDeref {x} {s} {e}) (sAssignDeref {.p} {s} {e}) xp = ⟨ heap , ⟨ xp , refl ⟩ ⟩
soundness (hSeq HT1 HT2) (sSeq BS1 BS2) xp = soundness HT2 BS2 (soundness HT1 BS1 xp) 
soundness (hIf HT1 HT2) (sIfTrue x BS) xp = inj₁ (soundness HT1 BS ⟨ xp , x ⟩)
soundness (hIf HT1 HT2) (sIfFalse x BS) xp = inj₂ (soundness HT2 BS ⟨ xp , x ⟩)
soundness {p = p} (hWhile x HT) BS xp = lemma (λ BS' xp' eq → soundness HT BS' ⟨ xp' , eq ⟩) BS (x p xp) 
soundness (hAssert x1) (sAssert x) xp = xp
soundness (hConsequence HT x1 x2) BS xp = x2 (soundness HT BS (x1 xp))  
  