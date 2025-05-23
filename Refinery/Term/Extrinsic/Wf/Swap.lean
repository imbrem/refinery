import Refinery.Term.Extrinsic.Wf.DerivedRewrite

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α}

def Eqv.antipair {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γl A) (b : Eqv R Γr B) : Eqv R Γ (Ty.tensor A B)
  := .reswap (.pair hΓ.comm b a)

theorem Eqv.reswap_pair {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γl A) (b : Eqv R Γr B) : (pair hΓ a b).reswap = antipair hΓ.comm b a
  := by induction a, b using quotInd₂; apply of_tm; simp [Wf.let₂, Wf.pair]

variable [R.UWkCongr]

theorem Eqv.antipair_def' {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γl A) (b : Eqv R Γr B)
  : a.antipair hΓ b
  = b.let₁ hΓ ((a.wk0 ⟨B, 0⟩).let₁ (Γl.erase_left).left
    (.pair Γl.erase.erase_left.right.left .bv0 .bv1))
  := by
  rw [antipair, reswap, let₂_beta]
  induction a, b using quotInd₂
  apply of_tm
  simp [Wf.let₁, Wf.pair, Wf.bv0, Wf.bv1]

theorem Eqv.antipair_comm {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γl A) (b : Eqv R Γr B)
  [ha : a.HasEff ea] [hb : b.HasEff eb] (he : ea ⇌ eb)
  : a.antipair hΓ b = a.pair hΓ b
  := by rw [antipair_def', bind_pair_comm hΓ a b he]

theorem Eqv.antipair_comm_left {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γl A) (b : Eqv R Γr B) [ha : a.HasEff ⊥]
  : a.antipair hΓ b = a.pair hΓ b
  := antipair_comm hΓ a b (eb := ⊤) HasCommRel.commutes_bot_left

theorem Eqv.antipair_comm_right {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γl A) (b : Eqv R Γr B) [hb : b.HasEff ⊥]
  : a.antipair hΓ b = a.pair hΓ b
  := antipair_comm hΓ a b (ea := ⊤) HasCommRel.commutes_bot_right

theorem Eqv.reswap_antipair {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γl A) (b : Eqv R Γr B) : (antipair hΓ a b).reswap = pair hΓ.comm b a
  := by rw [antipair, reswap_reswap]

def Eqv.swap0 {Γ : Ctx? α} {A B : Ty α} {x : Var? α}
  (a : Eqv R ((Γ.cons x).cons ⟨A, ⊤⟩) B) : Eqv R ((Γ.cons ⟨A, ⊤⟩).cons x) B
  := .let₁ (Ctx?.erase_right _).right.left .bv1 (a.wk2 (x := ⟨A, 0⟩))

theorem Eqv.swap0_def {Γ : Ctx? α} {A B : Ty α} {x : Var? α}
  (a : Eqv R ((Γ.cons x).cons ⟨A, ⊤⟩) B)
  : a.swap0 = .let₁ (Ctx?.erase_right _).right.left .bv1 (a.wk2 (x := ⟨A, 0⟩))
  := rfl

theorem Eqv.swap0_pwk {Γ Γl Γr : Ctx? α} {A B : Ty α} {x y z : Var? α}
  (hΓ : Γ.SSplit ((Γl.cons x).cons y) ((Γr.cons ⟨A, ⊤⟩).cons z))
  [hΓr : Γr.del] [hx : x.del] [hz : z.del]
  (a : Eqv R ((Γl.cons y).cons ⟨A, ⊤⟩) B)
  : let₁ hΓ .bv1 (a.wk2 _) = a.swap0.pwk hΓ.pwk_swap0
  := by induction a using quotInd; apply of_tm; simp [Wf.let₁, Wf.bv1, Wf.wk2, Wf.pwk]

def Eqv.swap0_swap0 {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R ((Γ.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) : a.swap0.swap0 = a
  := calc
  _ = Eqv.let₁ (Ctx?.erase_right _).right .bv0 (a.wk1 (x := ⟨B, 0⟩))
    := by
      induction a using quotInd with
      | h a =>
      apply sound
      apply Wf.eqv.coh_out
      apply Wf.pre_beta_pureIIn
      simp
      simp [Wf.wk2, Wf.subst, Wf.let₁, Wf.wk1, Wf.bv0, Wf.bv1]
      constructor
      rfl
      rw [<-subst_renIn, <-subst_renIn, <-subst_ofRen]
      apply Subst.subst_eqOn_fvi
      intro x hx
      simp [Subst.renIn, Subst.ofRen]
      cases x using Nat.cases2 with
      | zero => rfl
      | one => rfl
      | rest x =>
        simp [SubstDS.refl_get]
        split
        rfl
        have ha := a.deriv.fvi_le_length
        simp at ha
        omega
  _ = _
    := by
    conv => rhs; rw [<-a.let₁_bv0]
    induction a using quotInd
    exact of_tm rfl

theorem Eqv.swap0_injective {Γ : Ctx? α} {A B C : Ty α}
  (a b : Eqv R ((Γ.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) (h : a.swap0 = b.swap0) : a = b
  := by rw [<-a.swap0_swap0, <-b.swap0_swap0, h]

theorem Eqv.let_comm_swap0 {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm) {ea eb : ε}
  (a : Eqv R Γr A) (b : Eqv R Γm B) (c : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  [ha : a.HasEff ea] [hb : b.HasEff eb] (he : ea ⇌ eb)
  : a.let₁ hΓ ((b.wk0 ⟨A, 0⟩).let₁ (hΓc.cons (.left _)) c)
  = b.let₁ (hΓ.comm.s1_23_12_3 hΓc)
    ((a.wk0 ⟨B, 0⟩).let₁ ((hΓ.comm.s1_23_12 hΓc).comm.cons (.left _)) c.swap0)
  := by rw [Eqv.let_comm hΓ hΓc a b c he, swap0]

theorem Eqv.let_pure_comm_swap0  {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γr A) (b : Eqv R Γm B) (c : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  [ha : a.HasEff ⊥]
  : a.let₁ hΓ ((b.wk0 ⟨A, 0⟩).let₁ (hΓc.cons (.left _)) c)
  = b.let₁ (hΓ.comm.s1_23_12_3 hΓc)
    ((a.wk0 ⟨B, 0⟩).let₁ ((hΓ.comm.s1_23_12 hΓc).comm.cons (.left _)) c.swap0)
  := let_comm_swap0 hΓ hΓc a b c (eb := ⊤) HasCommRel.commutes_bot_left

theorem Eqv.let_comm_pure_swap0 {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γr A) (b : Eqv R Γm B) (c : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  [hb : b.HasEff ⊥]
  : a.let₁ hΓ ((b.wk0 ⟨A, 0⟩).let₁ (hΓc.cons (.left _)) c)
  = b.let₁ (hΓ.comm.s1_23_12_3 hΓc)
    ((a.wk0 ⟨B, 0⟩).let₁ ((hΓ.comm.s1_23_12 hΓc).comm.cons (.left _)) c.swap0)
  := let_comm_swap0 hΓ hΓc a b c (ea := ⊤) HasCommRel.commutes_bot_right

theorem Eqv.wk2_swap0 {Γ : Ctx? α} {A B : Ty α} {x : Var? α} {y : Var? α} [hy : y.del]
  (a : Eqv R ((Γ.cons x).cons ⟨A, ⊤⟩) B)
  : a.swap0.wk2 y = (a.wk2 y).swap0
  := by
  induction a using quotInd; apply of_tm
  simp [Wf.let₁, Wf.wk2, Wf.bv1, ren_ren]; congr 1; ext x; cases x using Nat.cases2 <;> rfl

theorem Eqv.let₂_reswap
  {A B C} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γr (.tensor A B)) (b : Eqv R ((Γl.cons ⟨B, ⊤⟩).cons ⟨A, ⊤⟩) C)
  : a.reswap.let₂ hΓ b = a.let₂ hΓ b.swap0
  := by
  rw [reswap, let₂_let₂, let₂_beta]
  conv => rhs; rw [<-a.let₂_eta, let₂_let₂]
  congr 1
  rw [
    let₂_beta, wk0_bv0, wk0_bv1, wk2_swap0, swap0_pwk, swap0_swap0, <-wk1_bv1,
    wk1_let₁_anti,
  ]
  apply Eq.trans _ (let₁_bv0 _)
  induction a, b using quotInd₂
  exact of_tm rfl

def Eqv.swap0₂ {Γ : Ctx? α} {A B C : Ty α} {x : Var? α}
  (a : Eqv R (((Γ.cons x).cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  : Eqv R (((Γ.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons x) C
  := .let₁ Γ.erase_right.right.left.left .bv2
      (.let₁ Γ.erase_right.left.right.left.left .bv2
        ((a.wk3 _).wk3 _)
      )

def Eqv.unswap0₂ {Γ : Ctx? α} {A B C D : Ty α}
  (a : Eqv R (((Γ.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
  : Eqv R (((Γ.cons ⟨C, ⊤⟩).cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) D
  :=  .let₁ Γ.erase_right.right.left.left .bv2 (a.wk3 _)
