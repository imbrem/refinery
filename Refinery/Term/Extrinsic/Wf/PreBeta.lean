import Refinery.Term.Extrinsic.Refinement.Wk.Relation
import Refinery.Term.Extrinsic.Wf.Wk
import Refinery.Term.Extrinsic.Wf.Effect
import Refinery.Term.Extrinsic.FreeVar

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term


variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]
          {R : DRWS φ α}

theorem Wf.pre_beta_pos  {Γ Γl Γr : Ctx? α} {A : Ty α}
  (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A) (q : Quant) (hq : q ⊓ quant A ≤ quant Γr)
  (b : Wf R (Γl.cons ⟨A, q⟩) B)
  {el er} [ha : a.HasEff el] [hb : b.HasEff er] (he : el ⇀ er)
  (heq : q ⊓ quant A ≤ (pquant el).pos)
  : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp))) ≤ b.subst (SubstDS.subst0 hΓ a.deriv q hq)
    := by
    apply DRWS.uniform.base
    apply DRWS.refStep.beta
    apply DRWS.Beta.beta_pos <;> assumption

theorem Wf.pre_beta_neg {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A) (q : Quant) (hq : q ⊓ quant A ≤ quant Γr)
    (b : Wf R (Γl.cons ⟨A, q⟩) B)
    {el er} [ha : a.HasEff el] [hb : b.HasEff er] (he : el ↽ er)
    (heq : q ⊓ quant A ≤ (pquant el).neg)
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≥ b.subst (SubstDS.subst0 hΓ a.deriv q hq)
    := by
    apply DRWS.uniform.base
    apply DRWS.refStep.beta
    apply DRWS.Beta.beta_neg <;> assumption

theorem Wf.pre_beta {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A) (q : Quant) (hq : q ⊓ quant A ≤ quant Γr)
    (b : Wf R (Γl.cons ⟨A, q⟩) B)
    {el er} [ha : a.HasEff el] [hb : b.HasEff er] (he : el ⇌ er)
    (heq : q ⊓ quant A ≤ (pquant el))
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≈ b.subst (SubstDS.subst0 hΓ a.deriv q hq)
    := ⟨pre_beta_pos hΓ a q hq b he.left heq.left, pre_beta_neg hΓ a q hq b he.right heq.right⟩

theorem Wf.pre_beta_pureIn {B} {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A) (q : Quant) (hq : q ⊓ quant A ≤ quant Γr)
    (b : Wf R (Γl.cons ⟨A, q⟩) B)
    [ha : a.HasEff ⊥]
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≈ b.subst (SubstDS.subst0 hΓ a.deriv q hq)
    := pre_beta hΓ a q hq b (commutes_bot_left (r := ⊤)) (by simp [OrderedPQuant.pquant_bot])

theorem Wf.pre_beta_pureLin {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A)
    (b : Wf R (Γl.cons ⟨A, 1⟩) B)
    [ha : a.HasEff ⊥]
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≈ b.subst (SubstDS.subst0 hΓ a.deriv 1 bot_le)
    := pre_beta_pureIn hΓ a 1 bot_le b

theorem Wf.pre_beta_pureLout {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A)
    (b : Wf R (Γl.cons ⟨A, 1⟩) B)
    [hb : b.HasEff ⊥]
    : a.let₁ hΓ (b.pwk ((Ctx?.PWk.refl Γl).cons (by simp)))
    ≈ b.subst (SubstDS.subst0 hΓ a.deriv 1 bot_le)
    := pre_beta hΓ a 1 bot_le b (commutes_bot_right (l := ⊤)) bot_le

theorem Wf.pre_beta_pureIIn {B} {Γ Γl Γr : Ctx? α} {A : Ty α}
    (hΓ : Γ.SSplit Γl Γr) (a : Wf R Γr A) (hq : quant A ≤ quant Γr)
    (b : Wf R (Γl.cons ⟨A, ⊤⟩) B)
    [ha : a.HasEff ⊥]
    : a.let₁ hΓ b
    ≈ b.subst (SubstDS.subst0 hΓ a.deriv ⊤ hq)
    := (pre_beta_pureIn hΓ a ⊤ hq b).coh rfl rfl

theorem Wf.let₁_eta_pwk {Γ Γl Γr : Ctx? α}
  {A : Ty α} (a : Wf R Γr A) (hΓ : Γ.SSplit Γl Γr) [hΓl : Γl.del]
  : a.let₁ hΓ .bv0 ≈ a.pwk (hΓ.pwk_left_del) := by
  apply (Wf.pre_beta_pureLout hΓ a .bv0 (hb := by simp)).coh <;> rfl

theorem Wf.let₁_eta' {Γ : Ctx? α} {A : Ty α}
  (a : Wf R Γ A) (hΓ : Γ.SSplit Γl Γ) [hΓl : Γl.del] : a.let₁ hΓ .bv0 ≈ a := by
  apply (Wf.pre_beta_pureLout hΓ a .bv0 (hb := by simp)).coh <;> rfl

theorem Wf.let₁_eta {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A) : a.let₁ Γ.erase_left .bv0 ≈ a
:= a.let₁_eta' _

theorem Eqv.let₁_eta_pwk [R.UWkCongr] {Γ Γl Γr : Ctx? α}
  {A : Ty α} (a : Eqv R Γr A) (hΓ : Γ.SSplit Γl Γr) [hΓl : Γl.del]
  : a.let₁ hΓ .bv0 = a.pwk (hΓ.pwk_left_del) := by
  induction a using Eqv.quotInd; apply sound; apply Wf.let₁_eta_pwk

theorem Eqv.let₁_eta'
  {Γ : Ctx? α} {A : Ty α} (a : Eqv R Γ A) (hΓ : Γ.SSplit Γl Γ) [hΓl : Γl.del]
  : a.let₁ hΓ .bv0 = a := by
  induction a using Eqv.quotInd; apply sound; apply Wf.let₁_eta'

theorem Eqv.let₁_eta {Γ : Ctx? α} {A : Ty α} (a : Eqv R Γ A) : a.let₁ Γ.erase_left .bv0 = a := by
  induction a using Eqv.quotInd; apply sound; apply Wf.let₁_eta

theorem Wf.let₁_bv0 {Γ : Ctx? α} {A B : Ty α} (a : Wf R (Γ.cons ⟨A, ⊤⟩) B)
  : Wf.bv0.let₁ (Γ.erase_right.cons (.right ⟨A, ⊤⟩)) (a.wk1 ⟨A, 0⟩) ≈ a
  := by
    apply (Wf.pre_beta_pureIn
      (Γ.erase_right.cons (.right ⟨A, ⊤⟩)) .bv0 (quant A) (by simp)
        ((a.pwk ((Ctx?.PWk.refl _).cons (.wk (by simp)))).wk1 _) (ha := by simp)).coh
    · rfl
    · cases a;
      simp only [subst, EQuant.coe_top, pwk, wk1, ← subst_renIn]
      apply Subst.subst1_fvi
      intro x hx
      cases x; rfl
      simp [SubstDS.refl, SubstDS.refl_get]
      split
      rfl
      have hd := Deriv.fvi_le_length (by assumption)
      simp only [Ctx?.length_cons] at hd
      omega

theorem Eqv.let₁_bv0 [R.UWkCongr] {Γ : Ctx? α} {A B : Ty α} (a : Eqv R (Γ.cons ⟨A, ⊤⟩) B)
  : Eqv.bv0.let₁ (Γ.erase_right.cons (.right ⟨A, ⊤⟩)) (a.wk1 ⟨A, 0⟩) = a
  := by induction a using Eqv.quotInd; apply sound; apply Wf.let₁_bv0

theorem Eqv.let₁_unit_anti [R.UWkCongr] {Γ : Ctx? α} {A : Ty α} (a : Eqv R Γ A)
  : a = (Eqv.unit _).let₁ Γ.erase_right (a.wk0 ⟨.unit, ⊤⟩)
  := by
  induction a using Eqv.quotInd with
  | h a =>
  apply sound
  apply Setoid.symm
  apply (Wf.pre_beta_pureIn Γ.erase_right (Wf.unit _) _ (by simp) (a.wk0 ⟨.unit, ⊤⟩) (ha := _)).coh
  rfl
  simp [Wf.subst, Wf.wk0, <-subst_renIn]
  apply Subst.subst1_fvi
  intro x hx
  simp [SubstDS.refl_get]
  exact lt_of_lt_of_le hx a.deriv.fvi_le_length
  reduce
  infer_instance

theorem Wf.bind_pwk_inl {Γ Γl Γr : Ctx? α}
  {A : Ty α} (a : Wf R Γr A) (hΓ : Γ.SSplit Γl Γr) [hΓl : Γl.del]
  : a.let₁ hΓ (.inl A B .bv0) ≈ (a.pwk (hΓ.pwk_left_del)).inl A B := by
  apply (Wf.pre_beta_pureLout hΓ a (.inl A B .bv0) (hb := by simp [Wf.HasEff, inl, bv0])).coh
  <;> rfl

theorem Wf.bind_inl' {Γ : Ctx? α} {A : Ty α}
  (a : Wf R Γ A) (hΓ : Γ.SSplit Γl Γ) [hΓl : Γl.del]
  : a.let₁ hΓ (.inl A B .bv0) ≈ a.inl A B := by
  apply (Wf.pre_beta_pureLout hΓ a (.inl A B .bv0) (hb := by simp [Wf.HasEff, inl, bv0])).coh
  <;> rfl

theorem Wf.bind_inl {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A)
  : a.let₁ Γ.erase_left (.inl A B .bv0) ≈ a.inl A B
  := a.bind_inl' _

theorem Eqv.bind_pwk_inl [R.UWkCongr] {Γ Γl Γr : Ctx? α}
  {A : Ty α} (a : Eqv R Γr A) (hΓ : Γ.SSplit Γl Γr) [hΓl : Γl.del]
  : a.let₁ hΓ (.inl A B .bv0) = (a.pwk (hΓ.pwk_left_del)).inl A B := by
  induction a using Eqv.quotInd; apply sound; apply Wf.bind_pwk_inl

theorem Eqv.bind_inl' {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) (hΓ : Γ.SSplit Γl Γ) [hΓl : Γl.del]
  : a.let₁ hΓ (.inl A B .bv0) = a.inl A B := by
  induction a using Eqv.quotInd; apply sound; apply Wf.bind_inl'

theorem Eqv.bind_inl {Γ : Ctx? α} {A : Ty α} (a : Eqv R Γ A)
  : a.let₁ Γ.erase_left (.inl A B .bv0) = a.inl A B
  := a.bind_inl' _

theorem Wf.bind_pwk_inr {Γ Γl Γr : Ctx? α}
  {A : Ty α} (a : Wf R Γr A) (hΓ : Γ.SSplit Γl Γr) [hΓl : Γl.del]
  : a.let₁ hΓ (.inr B A .bv0) ≈ (a.pwk (hΓ.pwk_left_del)).inr B A := by
  apply (Wf.pre_beta_pureLout hΓ a (.inr B A .bv0) (hb := by simp [Wf.HasEff, inr, bv0])).coh
  <;> rfl

theorem Wf.bind_inr' {Γ : Ctx? α} {A : Ty α}
  (a : Wf R Γ A) (hΓ : Γ.SSplit Γl Γ) [hΓl : Γl.del]
  : a.let₁ hΓ (.inr B A .bv0) ≈ a.inr B A := by
  apply (Wf.pre_beta_pureLout hΓ a (.inr B A .bv0) (hb := by simp [Wf.HasEff, inr, bv0])).coh
  <;> rfl

theorem Wf.bind_inr {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A)
  : a.let₁ Γ.erase_left (.inr B A .bv0) ≈ a.inr B A
  := a.bind_inr' _

theorem Eqv.bind_pwk_inr [R.UWkCongr] {Γ Γl Γr : Ctx? α}
  {A : Ty α} (a : Eqv R Γr A) (hΓ : Γ.SSplit Γl Γr) [hΓl : Γl.del]
  : a.let₁ hΓ (.inr B A .bv0) = (a.pwk (hΓ.pwk_left_del)).inr B A := by
  induction a using Eqv.quotInd; apply sound; apply Wf.bind_pwk_inr

theorem Eqv.bind_inr' {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) (hΓ : Γ.SSplit Γl Γ) [hΓl : Γl.del]
  : a.let₁ hΓ (.inr B A .bv0) = a.inr B A := by
  induction a using Eqv.quotInd; apply sound; apply Wf.bind_inr'

theorem Eqv.bind_inr {Γ : Ctx? α} {A : Ty α} (a : Eqv R Γ A)
  : a.let₁ Γ.erase_left (.inr B A .bv0) = a.inr B A
  := a.bind_inr' _

theorem Wf.bind_pwk_abort {Γ Γl Γr : Ctx? α}
  {A : Ty α} (a : Wf R Γr .empty) (hΓ : Γ.SSplit Γl Γr) [hΓl : Γl.del]
  : a.let₁ hΓ (.abort A .bv0) ≈ (a.pwk (hΓ.pwk_left_del)).abort A := by
  apply (Wf.pre_beta_pureLout hΓ a (.abort A .bv0) (hb := by simp [Wf.HasEff, abort, bv0])).coh
  <;> rfl

theorem Wf.bind_abort' {Γ : Ctx? α} {A : Ty α}
  (a : Wf R Γ .empty) (hΓ : Γ.SSplit Γl Γ) [hΓl : Γl.del]
  : a.let₁ hΓ (.abort A .bv0) ≈ a.abort A := by
  apply (Wf.pre_beta_pureLout hΓ a (.abort A .bv0) (hb := by simp [Wf.HasEff, abort, bv0])).coh
  <;> rfl

theorem Wf.bind_abort {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ .empty)
  : a.let₁ Γ.erase_left (.abort A .bv0) ≈ a.abort A
  := a.bind_abort' _
