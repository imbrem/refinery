import Discretion.Quant.Class

namespace Refinery

open HasQuant

universe u v

variable {α : Type u} {β : Type v}

inductive Ty (α : Type u) : Type u where
  | of : α → Ty α
  | unit : Ty α
  | empty : Ty α
  | tensor : Ty α → Ty α → Ty α
  | coprod : Ty α → Ty α → Ty α
  deriving DecidableEq

def Ty.map {α β : Type u} (f : α → β) : Ty α → Ty β
  | Ty.of a => Ty.of (f a)
  | Ty.unit => Ty.unit
  | Ty.empty => Ty.empty
  | Ty.tensor A B => Ty.tensor (A.map f) (B.map f)
  | Ty.coprod A B => Ty.coprod (A.map f) (B.map f)

def Ty.bind {α β : Type u} (f : α → Ty β) : Ty α → Ty β
  | Ty.of a => f a
  | Ty.unit => Ty.unit
  | Ty.empty => Ty.empty
  | Ty.tensor A B => Ty.tensor (A.bind f) (B.bind f)
  | Ty.coprod A B => Ty.coprod (A.bind f) (B.bind f)

def Ty.flatten {α : Type u} : Ty (Ty α) → Ty α
  | Ty.of A => A
  | Ty.unit => Ty.unit
  | Ty.empty => Ty.empty
  | Ty.tensor A B => Ty.tensor (Ty.flatten A) (Ty.flatten B)
  | Ty.coprod A B => Ty.coprod (Ty.flatten A) (Ty.flatten B)

variable [HasQuant α]

def Ty.q : Ty α → Quant
  | Ty.of a => quant a
  | Ty.unit => ⊤
  | Ty.empty => ⊤
  | Ty.tensor A B => A.q ⊓ B.q
  | Ty.coprod A B => A.q ⊓ B.q

instance Ty.instHasQuant : HasQuant (Ty α) := ⟨q⟩

@[simp] theorem Ty.quant_unit : quant (Ty.unit : Ty α) = ⊤ := rfl

@[simp] theorem Ty.quant_empty : quant (Ty.empty : Ty α) = ⊤ := rfl

@[simp] theorem Ty.quant_of (a : α) : quant (Ty.of a : Ty α) = quant a := rfl

@[simp]
theorem Ty.quant_tensor (A B : Ty α) : quant (Ty.tensor A B) = quant A ⊓ quant B := rfl

@[simp]
theorem Ty.quant_coprod (A B : Ty α) : quant (Ty.coprod A B) = quant A ⊓ quant B := rfl

instance IsAff.of (a : α) [ha : IsAff a] : IsAff (Ty.of a)
  := ⟨ha.del_le_quant⟩

instance IsRel.of (a : α) [ha : IsRel a] : IsRel (Ty.of a)
  := ⟨ha.copy_le_quant⟩

instance IsAff.unit : IsAff (Ty.unit (α := α)) := ⟨by simp⟩

instance IsRel.unit : IsRel (Ty.unit (α := α)) := ⟨by simp⟩

instance IsAff.empty : IsAff (Ty.empty (α := α)) := ⟨by simp⟩

instance IsRel.empty : IsRel (Ty.empty (α := α)) := ⟨by simp⟩

instance IsAff.tensor
  (A B : Ty α) [hA : IsAff A] [hB : IsAff B] : IsAff (Ty.tensor A B)
  := ⟨by simp⟩

instance IsRel.tensor
  (A B : Ty α) [hA : IsRel A] [hB : IsRel B] : IsRel (Ty.tensor A B)
  := ⟨by simp⟩

instance IsAff.coprod
  (A B : Ty α) [hA : IsAff A] [hB : IsAff B] : IsAff (Ty.coprod A B)
  := ⟨by simp⟩

instance IsRel.coprod
  (A B : Ty α) [hA : IsRel A] [hB : IsRel B] : IsRel (Ty.coprod A B)
  := ⟨by simp⟩

theorem IsAff.of_inv (a : α) [ha : IsAff (Ty.of a)] : IsAff a := ⟨ha.del_le_quant⟩

theorem IsAff.tensor_left (A B : Ty α) [hAB : IsAff (Ty.tensor A B)] : IsAff A
  := ⟨(le_inf_iff.mp hAB.del_le_quant).1⟩

theorem IsAff.tensor_right (A B : Ty α) [hAB : IsAff (Ty.tensor A B)] : IsAff B
  := ⟨(le_inf_iff.mp hAB.del_le_quant).2⟩

theorem IsAff.coprod_left (A B : Ty α) [hAB : IsAff (Ty.coprod A B)] : IsAff A
  := ⟨(le_inf_iff.mp hAB.del_le_quant).1⟩

theorem IsAff.coprod_right (A B : Ty α) [hAB : IsAff (Ty.coprod A B)] : IsAff B
  := ⟨(le_inf_iff.mp hAB.del_le_quant).2⟩

theorem IsRel.of_inv (a : α) [ha : IsRel (Ty.of a)]
  : IsRel a := ⟨ha.copy_le_quant⟩

theorem IsRel.tensor_left (A B : Ty α) [hAB : IsRel (Ty.tensor A B)]
  : IsRel A := ⟨(le_inf_iff.mp hAB.copy_le_quant).1⟩

theorem IsRel.tensor_right (A B : Ty α) [hAB : IsRel (Ty.tensor A B)]
  : IsRel B := ⟨(le_inf_iff.mp hAB.copy_le_quant).2⟩

theorem IsRel.coprod_left (A B : Ty α) [hAB : IsRel (Ty.coprod A B)]
  : IsRel A := ⟨(le_inf_iff.mp hAB.copy_le_quant).1⟩

theorem IsRel.coprod_right (A B : Ty α) [hAB : IsRel (Ty.coprod A B)]
  : IsRel B := ⟨(le_inf_iff.mp hAB.copy_le_quant).2⟩

theorem IsAff.tensor_iff {A B : Ty α} : IsAff (Ty.tensor A B) ↔ IsAff A ∧ IsAff B :=
  ⟨λ h => ⟨IsAff.tensor_left A B, IsAff.tensor_right A B⟩,
   λ ⟨hA, hB⟩ => ⟨by simp [hA, hB]⟩⟩

theorem IsAff.coprod_iff {A B : Ty α} : IsAff (Ty.coprod A B) ↔ IsAff A ∧ IsAff B :=
  ⟨λ h => ⟨IsAff.coprod_left A B, IsAff.coprod_right A B⟩,
   λ ⟨hA, hB⟩ => ⟨by simp [hA, hB]⟩⟩

theorem IsRel.tensor_iff {A B : Ty α} : IsRel (Ty.tensor A B) ↔ IsRel A ∧ IsRel B :=
  ⟨λ h => ⟨IsRel.tensor_left A B, IsRel.tensor_right A B⟩,
   λ ⟨hA, hB⟩ => ⟨by simp [hA, hB]⟩⟩

theorem IsRel.coprod_iff {A B : Ty α} : IsRel (Ty.coprod A B) ↔ IsRel A ∧ IsRel B :=
  ⟨λ h => ⟨IsRel.coprod_left A B, IsRel.coprod_right A B⟩,
   λ ⟨hA, hB⟩ => ⟨by simp [hA, hB]⟩⟩
