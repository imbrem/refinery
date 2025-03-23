import Refinery.Term.Syntax.FreeVar
import Refinery.Term.Extrinsic.Typing

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

theorem Deriv.fvi_le_length
  {Γ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)} (da : Γ ⊢ a : A) : a.fvi ≤ Γ.length := by
  induction da with
  | bv hΓ =>
    have _ := hΓ.length_lt;
    rw [fvi]; omega
  | _ =>
    try (
      rename Ctx?.SSplit _ _ _ => hΓ;
      have hΓl := hΓ.left_length.symm;
      have hΓr := hΓ.right_length.symm
    )
    simp [fvi, *] at * <;> simp [*]
