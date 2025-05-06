import Refinery.Ctx.SSplit

namespace Refinery

variable {α : Type u}

def Ctx?.append (Γ Δ : Ctx? α) : Ctx? α := List.append Δ Γ

instance Ctx?.instAppend : Append (Ctx? α) := ⟨Ctx?.append⟩

@[simp]
theorem Ctx?.append_nil (Γ : Ctx? α) : Γ ++ .nil = Γ := rfl

@[simp]
theorem Ctx?.nil_append (Δ : Ctx? α) : Ctx?.nil ++ Δ = Δ := List.append_nil Δ

@[simp]
theorem Ctx?.append_cons (Γ Δ : Ctx? α) (v : Var? α)
  : Γ ++ (Δ.cons v) = (Γ ++ Δ).cons v := rfl

theorem Ctx?.append_assoc (Γ Δ Θ : Ctx? α)
  : (Γ ++ Δ) ++ Θ = Γ ++ (Δ ++ Θ) := (List.append_assoc Θ Δ Γ).symm

def Ctx?.rev (Γ : Ctx? α) : Ctx? α := List.reverse Γ

theorem Ctx?.rev_append (Γ Δ : Ctx? α)
  : (Γ ++ Δ).rev = Δ.rev ++ Γ.rev := List.reverse_append

@[simp] theorem Ctx?.rev_nil : Ctx?.nil.rev = Ctx?.nil (α := α) := rfl

@[simp] theorem Ctx?.rev_rev (Γ : Ctx? α) : Γ.rev.rev = Γ := List.reverse_reverse Γ

variable [HasQuant α]

def Ctx?.Wk.append {Γ Γ' Δ Δ' : Ctx? α}
  (ρΓ : Γ'.Wk Γ) (ρΔ : Δ'.Wk Δ) : (Γ' ++ Δ').Wk (Γ ++ Δ)
  := match ρΓ, ρΔ with
  | ρΓ, .nil => ρΓ
  | ρΓ, .cons ρΔ hvw => (ρΓ.append ρΔ).cons hvw
  | ρΓ, .skip ρΔ hv =>  (ρΓ.append ρΔ).skip hv

@[simp]
theorem Ctx?.Wk.append_nil {Γ Γ' : Ctx? α} (ρΓ : Γ'.Wk Γ)
  : ρΓ.append .nil = ρΓ := rfl

@[simp]
theorem Ctx?.Wk.append_cons
  {Γ Γ' Δ Δ' : Ctx? α} (ρΓ : Γ'.Wk Γ) (ρΔ : Δ'.Wk Δ) {v w : Var? α} (hvw : v.Wk w)
  : ρΓ.append (ρΔ.cons hvw) = (ρΓ.append ρΔ).cons hvw := rfl

@[simp]
theorem Ctx?.Wk.append_skip
  {Γ Γ' Δ Δ' : Ctx? α} (ρΓ : Γ'.Wk Γ) (ρΔ : Δ'.Wk Δ) {v : Var? α} (hv : v.del)
  : ρΓ.append (ρΔ.skip hv) = (ρΓ.append ρΔ).skip hv := rfl

def Ctx?.wkAppend (Γ Δ : Ctx? α) (v : Var? α) [hv : v.del]
  : (Γ.cons v ++ Δ).Wk (Γ ++ Δ) := match Δ with
  | .nil => Γ.wk0 v
  | .cons Δ w => (Γ.wkAppend Δ v).scons w

def Ctx?.SSplit.append {Γ Γl Γr Δ Δl Δr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) (hΔ : Δ.SSplit Δl Δr) : (Γ ++ Δ).SSplit (Γl ++ Δl) (Γr ++ Δr)
  := match hΔ with
  | .nil => hΓ
  | .cons hΔ hvw => .cons (hΓ.append hΔ) hvw

def Ctx?.At.append {Γ} (hΓ : Γ.At v n) (Δ : Ctx? α) [hΔ : Δ.del] : (Γ ++ Δ).At v (n + Δ.length)
  := match Δ, hΔ with
  | .nil, _ => hΓ
  | .cons Δ _, hΔ => have _ := hΔ.tail; .there (hΓ.append Δ) hΔ.head

def Ctx?.At.append' {Γ} (hΓ : Γ.At v n) (Δ : Ctx? α) [hΔ : Δ.del] : (Γ ++ Δ).At v (Δ.length + n)
  := (hΓ.append Δ).cast rfl rfl (by rw [add_comm])

def Ctx?.atAppend (Γ Δ : Ctx? α) [hΓ : Γ.del] [hΔ : Δ.del] (v w : Var? α) (h : v.Wk w)
  : (Γ.cons v ++ Δ).At w Δ.length
  := match Δ, hΔ with
  | .nil, _ => .here hΓ h
  | .cons Δ _, hΔ => have _ := hΔ.tail; .there (Γ.atAppend Δ v w h) hΔ.head
