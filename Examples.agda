module Examples where

open import HoareTriples

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

initialState : ProgramState
initialState = record { variables = empty; heap = empty }

data IsEmpty : ProgramState → Set where
  isempty : IsEmpty record { variables = empty; heap = empty }

assertionExample : Assertion
assertionExample = assertion λ p → IsEmpty p

retrieveEmptyExample : retrieveNat 3 empty ≡ 0
retrieveEmptyExample = refl

retrieveFoundExample : retrieveNat 3 (2 := 5 v 3 := 7 v empty) ≡ 7
retrieveFoundExample = refl

evalExprExample : evalExpr (initialState withV ("x" := 6)) (Mul (Add (Num 3) (Num 4)) (Var "x")) ≡ 42
evalExprExample = refl
