import Refinery.Term.Extrinsic.Wf.PreBeta
import Refinery.Term.Extrinsic.Wf.Rewrite

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]
          {R : DRWS φ α}


def SubstDS.subst0₂ {Γ Γl Γc Γm Γr : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm) (da : Γm ⊢ a : A) (db : Γr ⊢ b : B)
  (qa qb : Quant) (hqa : qa ⊓ quant A ≤ quant Γm) (hqb : qb ⊓ quant B ≤ quant Γr)
  : SubstDS φ Γ ((Γl.cons ⟨A, qa⟩).cons ⟨B, qb⟩)
  := .cons hΓ
      (.cons hΓc (.refl Γl) (.valid _ _ da hqa))
      (.valid _ _ db hqb)

def SubstDS.subst0₂' {Γ Γl Γc Γm Γr : Ctx? α} {A B : Ty α} {a b : Term φ (Ty α)}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr) (da : Γm ⊢ a : A) (db : Γr ⊢ b : B)
  (qa qb : Quant) (hqa : qa ⊓ quant A ≤ quant Γm) (hqb : qb ⊓ quant B ≤ quant Γr)
  : SubstDS φ Γ ((Γl.cons ⟨A, qa⟩).cons ⟨B, qb⟩)
  := .subst0₂ (hΓ.s1_23_12_3 hΓc) (hΓ.s1_23_12 hΓc) da db qa qb hqa hqb

--TODO: generalize effects a bit here?

theorem Wf.pre_let₁_let₁_beta_pureIIn {Γ Γc Γl Γm Γr : Ctx? α} {A B C}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Wf R Γr A) (b : Wf R Γm B)
  (c : Wf R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  [ha : a.HasEff ⊥] [hb : b.HasEff ⊥]
  (hqa : quant A ≤ quant Γr) (hqb : quant B ≤ quant Γm)
  :  a.let₁ hΓ ((b.wk0 _).let₁ hΓc.left c)
  ≈ c.subst
    (SubstDS.subst0₂
      (hΓ.s12_3_1_23 hΓc.comm).comm
      (hΓ.s12_3_23 hΓc.comm) a.deriv b.deriv ⊤ ⊤ hqa hqb)
  := calc
  _ ≈ a.let₁ hΓ
    (c.subst (SubstDS.subst0 hΓc.left (b.wk0 ⟨A, 0⟩).deriv ⊤ (by simp [hqb])))
    := by apply eqv.let₁_congr; rfl; apply pre_beta_pureIIn
  _ ≈ (c.subst (SubstDS.subst0 hΓc.left (b.wk0 ⟨A, 0⟩).deriv ⊤ (by simp [hqb]))).subst
    (SubstDS.subst0 hΓ a.deriv ⊤ hqa) := by apply pre_beta_pureIIn
  _ ≈ _ := by
    apply eqv.of_tm
    simp [subst, subst_subst, wk0]
    apply Subst.subst_eqOn_fvi
    intro x hx
    cases x using Nat.cases2 with
    | zero =>
      simp [SubstDS.subst0₂', wk0, <-subst_renIn]; apply Subst.subst1_fvi
      intro y hy
      simp [
        SubstDS.refl_get, Ctx?.SSplit.c1_23_13, Ctx?.SSplit.l12_3_1_23,
        hΓc.right_length, hΓ.right_length, lt_of_lt_of_le hy b.deriv.fvi_le_length
      ]
    | one => rfl
    | rest x =>
      simp [SubstDS.subst0, SubstDS.refl_get, SubstDS.subst0₂]
      split
      simp [SubstDS.refl_get, Ctx?.SSplit.c1_23_13, Ctx?.SSplit.l12_3_1_23, hΓc.left_length, *]
      rfl

theorem Wf.pre_let₂_beta_pureIIn {Γ Γc Γl Γm Γr : Ctx? α} {A B C}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Wf R Γm A) (b : Wf R Γr B)
  (c : Wf R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  [ha : a.HasEff ⊥] [hb : b.HasEff ⊥]
  (hqa : quant A ≤ quant Γm) (hqb : quant B ≤ quant Γr)
  : ((a.pair hΓc b).let₂ hΓ c) ≈ c.subst (SubstDS.subst0₂' hΓ hΓc a.deriv b.deriv ⊤ ⊤ hqa hqb)
  := calc
  _ ≈ a.let₁ (hΓ.s1_23_13_2 hΓc) ((b.wk0 _).let₁ (hΓ.s1_23_13 hΓc).left c) := a.let₂_beta hΓ hΓc b c
  _ ≈ _ := by
    apply eqv.coh_out
    apply pre_let₁_let₁_beta_pureIIn
    assumption
    assumption
    simp [subst]
    congr
    ext x
    cases x using Nat.cases2 <;> rfl

def SubstDS.subst0₃ {Γ Γ123 Γ12 Γ1 Γ2 Γ3 Γ4 : Ctx? α} {A B C : Ty α} {a b c : Term φ (Ty α)}
  (hΓ : Γ.SSplit Γ123 Γ4) (hΓ123 : Γ123.SSplit Γ12 Γ3) (hΓ12 : Γ12.SSplit Γ1 Γ2)
  (da : Γ2 ⊢ a : A) (db : Γ3 ⊢ b : B) (dc : Γ4 ⊢ c : C) (qa qb qc : Quant)
  (hqa : qa ⊓ quant A ≤ quant Γ2) (hqb : qb ⊓ quant B ≤ quant Γ3) (hqc : qc ⊓ quant C ≤ quant Γ4)
  : SubstDS φ Γ (((Γ1.cons ⟨A, qa⟩).cons ⟨B, qb⟩).cons ⟨C, qc⟩)
  := .cons hΓ
      (.cons hΓ123
        (.cons hΓ12 (.refl Γ1) (.valid _ _ da hqa))
        (.valid _ _ db hqb))
      (.valid _ _ dc hqc)

theorem Wf.pre_let₁_let₁_let₁_beta_pureIIn {Γ Γ123 Γ12 Γ1 Γ2 Γ3 Γ4 : Ctx? α} {A B C D}
  (hΓ : Γ.SSplit Γ123 Γ4) (hΓ123 : Γ123.SSplit Γ12 Γ3) (hΓ12 : Γ12.SSplit Γ1 Γ2)
  (a : Wf R Γ4 A) (b : Wf R Γ3 B) (c : Wf R Γ2 C)
  (d : Wf R (((Γ1.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
  [ha : a.HasEff ⊥] [hb : b.HasEff ⊥] [hc : c.HasEff ⊥]
  (hqa : quant A ≤ quant Γ4) (hqb : quant B ≤ quant Γ3) (hqc : quant C ≤ quant Γ2)
  : a.let₁ hΓ ((b.wk0 _).let₁ hΓ123.left (((c.wk0 _).wk0 _).let₁ hΓ12.left.left d))
  ≈ d.subst
    (SubstDS.subst0₃
      ((hΓ.s12_3_1_23 hΓ123).s12_3_1_23 hΓ12.comm).comm
      (((hΓ.s12_3_1_23 hΓ123).s12_3_23 hΓ12.comm).comm.s12_3_1_23 (hΓ.s12_3_23 hΓ123)).comm
      (((hΓ.s12_3_1_23 hΓ123).s12_3_23 hΓ12.comm).comm.s12_3_23 (hΓ.s12_3_23 hΓ123)).comm
      a.deriv b.deriv c.deriv ⊤ ⊤ ⊤
      hqa hqb hqc)
  := calc
  _ ≈ a.let₁ hΓ (
    d.subst (SubstDS.subst0₂' (hΓ123.s12_3_1_23 hΓ12).left (hΓ123.s12_3_23 hΓ12).comm.left
      (b.wk0 ⟨A, 0⟩).deriv ((c.wk0 ⟨A, 0⟩)).deriv ⊤ ⊤ (by simp [hqb]) (by simp [hqc])))
    := by
      apply eqv.let₁_congr; rfl; apply eqv.coh_out
      apply pre_let₁_let₁_beta_pureIIn
      simp [hqb]
      simp [hqc]
      simp [subst]
      congr; ext x; cases x using Nat.cases2 <;> rfl
  _ ≈ _ := by
    apply eqv.coh_out
    apply pre_beta_pureIIn
    exact hqa
    simp [subst, subst_subst]
    apply Subst.subst_eqOn_fvi
    intro x hx
    cases x using Nat.cases3 with
    | zero =>
      simp [SubstDS.subst0₂', SubstDS.subst0₃, SubstDS.subst0₂, wk0, <-subst_renIn]
      apply Subst.subst1_fvi
      intro y hy
      simp [SubstDS.refl_get]
      convert lt_of_lt_of_le hy c.deriv.fvi_le_length using 1
      rw [hΓ123.left_length, hΓ12.right_length]
    | one =>
      simp [SubstDS.subst0, SubstDS.subst0₂', SubstDS.subst0₂, SubstDS.subst0₃, wk0, <-subst_renIn]
      apply Subst.subst1_fvi
      intro y hy
      simp [SubstDS.refl_get]
      convert lt_of_lt_of_le hy b.deriv.fvi_le_length using 1
      rw [hΓ123.right_length]
    | two => rfl
    | rest x =>
      simp [SubstDS.subst0, SubstDS.subst0₃, SubstDS.subst0₂, SubstDS.subst0₂', SubstDS.refl_get]
      split
      simp [SubstDS.refl_get]
      rw [hΓ123.left_length, hΓ12.left_length]
      assumption
      rfl
