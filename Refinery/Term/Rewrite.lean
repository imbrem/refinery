import Refinery.Term.Syntax
import Refinery.Signature

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v}

def CRWS (φ α) := Term φ α → Term φ α → Prop

inductive LetMove : CRWS φ α
  | let_op {f a A B b} :
    LetMove (.let₁ (.op f a) B b) (.let₁ a A (.let₁ (.op f (.bv 0)) A (↑¹ a)))
  | let_let₁ {a A b B c} :
    LetMove (.let₁ (.let₁ a A b) B c) (.let₁ a A (.let₁ b B (↑¹ c)))
  | let_let₂ {a A B b C c} :
    LetMove (.let₁ (.let₂ a A B b) C c) (.let₂ a A B (.let₁ b C (↑¹ (↑¹ c))))
  | let_case {a A B C b c d} :
    LetMove (.let₁ (.case a A B b c) C d) (.case a A B (.let₁ b C (↑¹ d)) (.let₁ c C (↑¹ d)))
  | let_abort {a A b} :
    LetMove (.let₁ (.abort A a) A b) (.abort A a)
