import Refinery.Term.Extrinsic.Subst.Basic
import Refinery.Term.Extrinsic.Effect

namespace Refinery

namespace Term

open HasQuant

open HasCommRel

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive Deriv?.HasEff
  : (e : ε) → {Γ : Ctx? α} → {v : Var? α} → {a : Term φ (Ty α)} → (Deriv? Γ v a) → Prop
  | valid
    {Γ : Ctx? α} {A} {q : Quant}
    {a : Term φ (Ty α)} (D : Γ ⊢ a : A) (hΓ : quant (Var?.mk A q) ≤ quant Γ)
    (ha : a.HasEff e) : HasEff e (.valid A q D hΓ)
  | zero {Γ : Ctx? α} (hΓ : Γ.del) (a A) : HasEff e (.zero hΓ a A)

attribute [class] Deriv?.HasEff

instance Deriv?.HasEff.instValid
    {Γ : Ctx? α} {A} {q : Quant}
    {a : Term φ (Ty α)} {D : Γ ⊢ a : A} {hΓ : quant (Var?.mk A q) ≤ quant Γ}
    [ha : a.HasEff e]
    : HasEff e (.valid A q D hΓ) := HasEff.valid D hΓ ha

instance Deriv?.HasEff.instZero {Γ : Ctx? α} [hΓ : Γ.del] {a A}
  : HasEff e (.zero hΓ a A) := HasEff.zero hΓ a A

theorem Deriv?.HasEff.mono
  {e e' : ε} (he : e ≤ e') {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} (D : Γ ⊢? a : v)
  (h : D.HasEff e) : D.HasEff e' := by cases h with
  | valid => constructor; apply Term.HasEff.mono <;> assumption
  | zero => constructor

instance Deriv?.HasEff.top
  {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} (D : Γ ⊢? a : v)
  : D.HasEff ⊤ := by cases D <;> infer_instance

inductive SubstDS.HasEff : (e : ε) → {Γ Δ : Ctx? α} → (SubstDS φ Γ Δ) → Prop
  | nil {e : ε} {Γ : Ctx? α} (hΓ : Γ.del) : HasEff e (.nil hΓ)
  | cons {e} {Γ Γl Γr Δ : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v)
    (hσ : σ.HasEff e) (ha : da.HasEff e)
    : HasEff e (σ.cons hΓ da)

attribute [class] SubstDS.HasEff

instance SubstDS.HasEff.instNil {Γ : Ctx? α} [hΓ : Γ.del] : HasEff e (.nil hΓ) := HasEff.nil hΓ

instance SubstDS.HasEff.instCons {Γ Γl Γr Δ : Ctx? α} {da : Γr ⊢? a : v} {hΓ : Γ.SSplit Γl Γr}
  {σ : SubstDS φ Γl Δ} [hσ : σ.HasEff e] [ha : da.HasEff e]
  : HasEff e (σ.cons hΓ da) := HasEff.cons hΓ σ da hσ ha

theorem SubstDS.HasEff.mono
  {e e' : ε} (he : e ≤ e') {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (h : σ.HasEff e)
  : σ.HasEff e' := by
  induction h with
  | nil => constructor
  | cons hΓ σ da hσ ha =>
    constructor; apply_assumption; assumption; apply Deriv?.HasEff.mono <;> assumption

instance SubstDS.HasEff.top
  {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ)
  : σ.HasEff ⊤ := by induction σ <;> infer_instance

--TODO: if HasEff and HasEff, then HasEff SubstD

inductive SubstDS.IsValid : (e : ε) → {Γ Δ : Ctx? α} → (SubstDS φ Γ Δ) → Prop
  | nil {e : ε} {Γ : Ctx? α} (hΓ : Γ.del) : IsValid e (.nil hΓ)
  | cons {e el er} {Γ Γl Γr Δ : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v)
    (hσ : σ.IsValid el) (ha : da.HasEff er)
    (hl : el ≤ e) (hr : er ≤ e) (hcomm : el ⇌ er)
    : IsValid e (σ.cons hΓ da)

attribute [class] SubstDS.IsValid

theorem SubstDS.IsValid.mono
  {e e' : ε} (he : e ≤ e') {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (h : σ.IsValid e)
  : σ.IsValid e' := by
  induction h with
  | nil => constructor
  | cons hΓ σ da hσ ha hl hr hcomm =>
    constructor; apply_assumption; assumption
    apply le_trans <;> assumption; apply le_trans <;> assumption; assumption

instance SubstDS.IsValid.has_eff
  (e : ε) {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [h : σ.IsValid e]
  : σ.HasEff e := by induction h with
  | nil => constructor
  | cons hΓ σ da hσ ha hl hr hcomm Iσ => constructor; exact Iσ.mono hl; exact ha.mono hr
