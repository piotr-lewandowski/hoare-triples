module Examples where

open import HoareTriples

data IsEmpty : ProgramState → Set where
  isempty : IsEmpty record { variables = empty; heap = empty }

test : Assertion
test = assertion λ p → IsEmpty p
