import Refinery.Term.Extrinsic.Wf.Rewrite
import Refinery.Term.Extrinsic.Wf.PreBeta
import Refinery.Term.Extrinsic.Wf.WkEffect

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α}

theorem Eqv.unit_pure_del {Γ : Ctx? α}
  [hΓ : Γ.del] (a : Eqv R Γ .unit) [ha : a.HasEff ⊥] : a = .unit Γ
  := by
  rw [<-a.terminal]
  cases ha with | mk ha =>
  apply Eqv.sound
  apply Wf.eqv.coh
  apply Wf.pre_beta_pureIn (A := .unit) Γ.erase_left _ (quant Γ) _
    (.unit _ (hΓ := by
      rw [Ctx?.cons_del_iff]
      constructor
      infer_instance
      constructor
      rw [quant]
      simp [Var?.hasQuant]
    )) (ha := ha)
  simp [Wf.pwk, Wf.unit]
  rfl
  rfl

theorem Eqv.unit_pure_unique {Γ : Ctx? α}
  [hΓ : Γ.del] (a b : Eqv R Γ .unit) [ha : a.HasEff ⊥] [hb : b.HasEff ⊥] : a = b
  := a.unit_pure_del.trans b.unit_pure_del.symm

variable [R.UWkCongr]

theorem Eqv.let₂_let₁ {Γ Γl Γc Γm Γr : Ctx? α} {A B C D}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (a : Eqv R Γr A)
    (b : Eqv R (Γm.cons ⟨A, ⊤⟩) (B.tensor C))
    (c : Eqv R ((Γl.cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
    : (a.let₁ hΓc b).let₂ hΓ c
    = a.let₁ (hΓ.s1_23_12_3 hΓc) (b.let₂ (((hΓ.s1_23_12 hΓc).cons (.right _))) (c.wk2 _)) := by
  rw [bind_let₂, let_let₁]
  congr 1
  conv => rhs; rw [bind_let₂]
  congr 1
  induction c using quotInd
  apply sound; apply Wf.eqv.of_tm
  simp [Wf.wk1, Wf.let₂, Wf.let₁, Wf.wk2, Wf.bv0, ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]

theorem Eqv.let₂_let₁_anti {Γ Γl Γc Γm Γr : Ctx? α} {A B C D}
    (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
    (a : Eqv R Γr A)
    (b : Eqv R (Γm.cons ⟨A, ⊤⟩) (B.tensor C))
    (c : Eqv R ((Γl.cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
    : a.let₁ hΓ (b.let₂ ((hΓc.cons (.right _))) (c.wk2 _))
    = (a.let₁ (hΓ.s12_3_23 hΓc) b).let₂ (hΓ.s12_3_1_23 hΓc) c := by
  rw [let₂_let₁]
  induction a, b, c using quotInd₃
  apply sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.let₂_let₁_anti' {Γ Γl Γc Γm Γr : Ctx? α} {A B C D}
    (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
    (a : Eqv R Γr A)
    (b : Eqv R (Γm.cons ⟨A, ⊤⟩) (B.tensor C))
    (c : Eqv R (((Γl.cons ⟨A, 0⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
    (c' : Eqv R ((Γl.cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
    (hc : c'.wk2 _ = c)
    : a.let₁ hΓ (b.let₂ ((hΓc.cons (.right _))) c)
    = (a.let₁ (hΓ.s12_3_23 hΓc) b).let₂ (hΓ.s12_3_1_23 hΓc) c' := by
  rw [<-hc, let₂_let₁_anti]


theorem Eqv.let₂_let₁_bv0_anti {Γ Γl Γr : Ctx? α} {A B C : Ty α}
    (hΓ : Γ.SSplit Γl Γr)
    (a : Eqv R Γr (A.tensor B))
    (c : Eqv R (((Γl.cons ⟨(A.tensor B), 0⟩).cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
    (c' : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
    (hc : c'.wk2 _ = c)
    : a.let₁ hΓ (let₂ (Γl.erase_right.cons (.right _)) .bv0 c)
    = a.let₂ hΓ c' := by
    rw [let₂_let₁_anti' (hc := hc)]
    conv => rhs; rw [<-a.let₁_eta]
    induction a, c' using quotInd₂
    exact Eqv.of_tm rfl

theorem Eqv.let₂_let₁_bv0_anti' {Γ Γl Γr : Ctx? α} {A B C : Ty α}
    (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm) [hΓm : Γm.del]
    (a : Eqv R Γr (A.tensor B))
    (c : Eqv R (((Γl.cons ⟨(A.tensor B), 0⟩).cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
    (c' : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
    (hc : c'.wk2 _ = c)
    : a.let₁ hΓ (let₂ (hΓc.cons (.right _)) .bv0 c)
    = a.let₂ hΓ (c'.pwk (((hΓc.pwk_right_del).scons _).scons _)) := by
    rw [let₂_let₁_anti' (hc := hc)]
    conv => rhs; rw [<-a.let₁_eta]
    induction a, c' using quotInd₂
    exact Eqv.of_tm rfl

theorem Eqv.let₂_let₂ {Γ Γl Γc Γm Γr : Ctx? α} {A B C D E}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (a : Eqv R Γr (A.tensor B))
    (b : Eqv R ((Γm.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) (C.tensor D))
    (c : Eqv R ((Γl.cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩) E)
    : (a.let₂ hΓc b).let₂ hΓ c
    = a.let₂ (hΓ.s1_23_12_3 hΓc)
      (b.let₂ (hΓ.s1_23_12 hΓc).right.right ((c.wk2 ⟨A, 0⟩).wk2 ⟨B, 0⟩))
  := by
  rw [bind_let₂, let_let₂]
  congr 1
  conv => rhs; rw [bind_let₂]
  congr 1
  induction c using quotInd
  apply sound; apply Wf.eqv.of_tm
  simp [Wf.wk1, Wf.let₂, Wf.wk2, Wf.bv0, ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
  rfl

theorem Eqv.let₂_let₂_erase {Γ Γl Γr : Ctx? α} {A B C D E : Ty α}
    (hΓ : Γ.SSplit Γl Γr)
    (a : Eqv R Γr (A.tensor B))
    (b : Eqv R ((Γr.erase.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) (C.tensor D))
    (c : Eqv R ((Γl.cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩) E)
    : (a.let₂ Γr.erase_left b).let₂ hΓ c
    = a.let₂ hΓ
      (b.let₂ (Γl.erase_right.cast_right hΓ.erase_eq).right.right ((c.wk2 ⟨A, 0⟩).wk2 ⟨B, 0⟩))
  := by rw [let₂_let₂]; induction a, b, c using quotInd₃; apply of_tm; simp [Wf.let₂]

theorem Eqv.let₂_let₂_anti {Γ Γl Γc Γm Γr : Ctx? α} {A B C D E}
    (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
    (a : Eqv R Γr (A.tensor B))
    (b : Eqv R ((Γm.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) (C.tensor D))
    (c : Eqv R ((Γl.cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩) E)
    : a.let₂ hΓ (b.let₂ hΓc.right.right ((c.wk2 _).wk2 _))
    = (a.let₂ (hΓ.s12_3_23 hΓc) b).let₂ (hΓ.s12_3_1_23 hΓc) c := by
  rw [let₂_let₂]
  induction a, b, c using quotInd₃
  apply sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.bind_pair {Γ Γl Γr : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γl A) (b : Eqv R Γr B)
  : a.pair hΓ b = .let₁ hΓ.comm a (.let₁ Γr.erase_left.left (b.wk0 _)
    (.pair (Ctx?.erase_left _).left.right .bv1 .bv0))
  := by
  rw [<-(a.pair hΓ b).let₂_eta, let₂_beta]
  induction a, b using quotInd₂
  apply sound
  apply Wf.eqv.of_tm
  rfl

theorem Eqv.bind_pair_anti' {Γ Γl Γr Γe : Ctx? α} [hΓe : Γe.del]
    (hΓ : Γ.SSplit Γl Γr)
    (hla : (Γl.cons ⟨A, ⊤⟩).SSplit (Γl.erase.cons ⟨A, ⊤⟩) (Γl.cons ⟨A, 0⟩))
    (hlb : ((Γl.erase.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).SSplit
      ((Γe.cons ⟨A, ⊤⟩).cons ⟨B, 0⟩)
      ((Γe.cons ⟨A, 0⟩).cons ⟨B, ⊤⟩))
    (a : Eqv R Γr A) (b : Eqv R Γl B)
  : .let₁ hΓ a (.let₁ hla (b.wk0 _) (.pair hlb .bv1 .bv0)) = a.pair hΓ.comm b
  := by
  conv => rhs; rw [bind_pair]
  induction a, b using quotInd₂; apply sound; apply Wf.eqv.of_tm; rfl

theorem Eqv.bind_pair_anti {A B} {Γ Γl Γr : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γr A) (b : Eqv R Γl B)
  : .let₁ hΓ a (.let₁ Γl.erase_left.left (b.wk0 _)
    (.pair (Ctx?.both _).left.right .bv1 .bv0))
    = a.pair hΓ.comm b
  := by rw [a.bind_pair_anti' hΓ]

theorem Eqv.bind_pair_left {Γ Γl Γr : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γl A) (b : Eqv R Γr B)
  : a.pair hΓ b = .let₁ hΓ.comm a (.pair (Γr.erase_left.cons (.left _)) .bv0 (b.wk0 ⟨A, 0⟩))
  := by
  rw [bind_pair]
  congr 1
  induction b using quotInd with
  | h b =>
  apply sound
  apply Wf.eqv.coh
  exact Wf.pre_beta_pureLout (Γr.erase_left.cons (.left _))
    (b.wk0 ⟨A, 0⟩)
    (.pair ((Γr.erase.erase_left.cons (.left _)).cons (.right _)) .bv1 .bv0)
  rfl
  rfl

--TODO: bind_pair_right_fwd

--TODO: bind_pair_right_bwd

theorem Eqv.bind_pair_right {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) (ea eb : ε)
  (a : Eqv R Γl A) (b : Eqv R Γr B)
  [ha : a.HasEff ea] [hb : b.HasEff eb] (he : ea ⇌ eb)
  : a.pair hΓ b
  = b.let₁ hΓ ((a.wk0 ⟨B, 0⟩).pair ((Γl.erase_right).cons (.right _)) .bv0)
  := by
  apply Eq.symm
  cases ha; induction hb
  rename_i ea a ha eb b hb
  apply sound
  apply Wf.eqv.coh
  exact Wf.pre_beta hΓ b 1 (by simp)
    (.pair ((Γl.erase_right).cons (.right _)) (a.wk0 ⟨B, 0⟩) .bv0)
    (hb := inferInstance) he.symm (by generalize pquant ea = p; cases p; constructor <;> simp)
  rfl
  simp only [Wf.subst, Wf.wk0, Wf.bv0, Wf.pair, subst, SubstDS.subst0_get_zero, pair.injEq,
    and_true]
  rw [<-Term.subst_renIn]
  apply Subst.subst1_fvi
  intro x hx
  simp [SubstDS.refl_get, lt_of_lt_of_le hx a.deriv.fvi_le_length]

theorem Eqv.bind_pair_right_pure_left {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γl A) (b : Eqv R Γr B)
  [ha : a.HasEff ⊥]
  : a.pair hΓ b
  = b.let₁ hΓ ((a.wk0 ⟨B, 0⟩).pair ((Γl.erase_right).cons (.right _)) .bv0)
  := bind_pair_right hΓ ⊥ ⊤ a b HasCommRel.commutes_bot_left

theorem Eqv.bind_pair_right_pure_right {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γl A) (b : Eqv R Γr B)
  [hb : b.HasEff ⊥]
  : a.pair hΓ b
  = b.let₁ hΓ ((a.wk0 ⟨B, 0⟩).pair ((Γl.erase_right).cons (.right _)) .bv0)
  := bind_pair_right hΓ ⊤ ⊥ a b HasCommRel.commutes_bot_right

--TODO: bind_pair_comm_fwd

--TODO: bind_pair_comm_bwd

theorem Eqv.bind_pair_comm {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) {ea eb : ε}
  (a : Eqv R Γl A) (b : Eqv R Γr B)
  [ha : a.HasEff ea] [hb : b.HasEff eb] (he : ea ⇌ eb)
  : a.pair hΓ b
  = b.let₁ hΓ ((a.wk0 ⟨B, 0⟩).let₁ ((Γl.erase_left).cons (.left _))
    (.pair (((Γl.erase.erase_left).cons (.right _)).cons (.left _)) .bv0 .bv1))
  := by
  rw [bind_pair_right _ _ _ _ _ he, bind_pair_left]
  induction a, b using quotInd₂
  apply sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.let_comm {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm) {ea eb : ε}
  (a : Eqv R Γr A) (b : Eqv R Γm B) (c : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  [ha : a.HasEff ea] [hb : b.HasEff eb] (he : ea ⇌ eb)
  : a.let₁ hΓ ((b.wk0 ⟨A, 0⟩).let₁ (hΓc.cons (.left _)) c)
  = b.let₁ (hΓ.comm.s1_23_12_3 hΓc)
    ((a.wk0 ⟨B, 0⟩).let₁ ((hΓ.comm.s1_23_12 hΓc).comm.cons (.left _))
      (.let₁ ((((Ctx?.erase_right _).cons (.right _))).cons (.left _)) .bv1 (c.wk2 ⟨B, 0⟩)))
  := by
  rw [
    let₂_beta_anti, <-let₁_bv0 (.let₁ _ .bv1 _), bind_pair_comm _ _ _ he, let₂_let₁, let₂_let₁,
    let₂_beta
  ]
  induction a, b, c using quotInd₃
  apply sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.let_comm_anti {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm) {ea eb : ε}
  (a : Eqv R Γm A) (b : Eqv R Γr B) (c : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  [ha : a.HasEff ea] [hb : b.HasEff eb] (he : ea ⇌ eb)
  : b.let₁ hΓ
    ((a.wk0 ⟨B, 0⟩).let₁ (hΓc.cons (.left _))
      (.let₁ ((((Ctx?.erase_right _).cons (.right _))).cons (.left _)) .bv1 (c.wk2 ⟨B, 0⟩)))
  = a.let₁ (hΓ.comm.s1_23_12_3 hΓc)
    ((b.wk0 ⟨A, 0⟩).let₁ ((hΓ.comm.s1_23_12 hΓc).comm.cons (.left _)) c)
  := by
  conv => rhs; rw [let_comm _ _ _ _ _ he]
  induction a, b, c using quotInd₃
  apply sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.let_comm_pure_left {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γr A) (b : Eqv R Γm B) (c : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  [ha : a.HasEff ⊥]
  : a.let₁ hΓ ((b.wk0 ⟨A, 0⟩).let₁ (hΓc.cons (.left _)) c)
  = b.let₁ (hΓ.comm.s1_23_12_3 hΓc)
    ((a.wk0 ⟨B, 0⟩).let₁ ((hΓ.comm.s1_23_12 hΓc).comm.cons (.left _))
      (.let₁ ((((Ctx?.erase_right _).cons (.right _))).cons (.left _)) .bv1 (c.wk2 ⟨B, 0⟩)))
  := by rw [let_comm (ea := ⊥) (eb := ⊤)]; apply HasCommRel.commutes_bot_left

theorem Eqv.let_comm_pure_right {A} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γr A) (b : Eqv R Γm B) (c : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  [hb : b.HasEff ⊥]
  : a.let₁ hΓ ((b.wk0 ⟨A, 0⟩).let₁ (hΓc.cons (.left _)) c)
  = b.let₁ (hΓ.comm.s1_23_12_3 hΓc)
    ((a.wk0 ⟨B, 0⟩).let₁ ((hΓ.comm.s1_23_12 hΓc).comm.cons (.left _))
      (.let₁ ((((Ctx?.erase_right _).cons (.right _))).cons (.left _)) .bv1 (c.wk2 ⟨B, 0⟩)))
  := by rw [let_comm (ea := ⊤) (eb := ⊥)]; apply HasCommRel.commutes_bot_right

def Eqv.reswap {A B} {Γ : Ctx? α} (a : Eqv R Γ (.tensor A B)) : Eqv R Γ (.tensor B A)
  := .let₂ (Γ.erase_left) a (.pair ((Γ.erase.erase_left.cons (.right _)).cons (.left _)) .bv0 .bv1)

theorem Eqv.reswap_let₁
  {A B C} {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
    (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) (.tensor B C))
  : (a.let₁ hΓ b).reswap = a.let₁ hΓ b.reswap := by
  rw [reswap, let₂_let₁]
  induction a, b using quotInd₂
  apply sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.reswap_let₂
  {A B C D} {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
    (a : Eqv R Γr (.tensor A B)) (b : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) (.tensor C D))
  : (a.let₂ hΓ b).reswap = a.let₂ hΓ b.reswap := by
  rw [reswap, let₂_let₂]
  induction a, b using quotInd₂
  apply sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.reswap_comm {A B} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) {ea eb : ε} (a : Eqv R Γl A) (b : Eqv R Γr B)
  [ha : a.HasEff ea] [hb : b.HasEff eb] (he : ea ⇌ eb)
  : (pair hΓ a b).reswap = (pair hΓ.comm b a) := by
  rw [reswap, let₂_beta]
  conv => rhs; rw [bind_pair_comm _ _ _ he.symm]
  induction a, b using quotInd₂
  apply sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.reswap_comm_left {A B} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γl A) (b : Eqv R Γr B) [ha : a.HasEff ⊥]
  : (pair hΓ a b).reswap = (pair hΓ.comm b a)
  := a.reswap_comm hΓ b (eb := ⊤) commutes_bot_left

theorem Eqv.reswap_comm_right {A B} {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γl A) (b : Eqv R Γr B) [hb : b.HasEff ⊥]
  : (pair hΓ a b).reswap = (pair hΓ.comm b a)
  := a.reswap_comm hΓ b (ea := ⊤) commutes_bot_right

theorem Eqv.reswap_reswap {A B} {Γ : Ctx? α} (a : Eqv R Γ (.tensor A B)) : a.reswap.reswap = a := by
  conv => lhs; rhs; rw [reswap]
  rw [reswap_let₂, reswap_comm_left]
  conv => rhs; rw [<-a.let₂_eta]
  induction a using quotInd
  apply sound; apply Wf.eqv.of_tm
  simp only [Wf.let₂, Wf.pair, Wf.bv0, Wf.bv1]

theorem Eqv.let_pair_right_wk0 {A B C} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) B) (c : Eqv R Γm C)
  : a.let₁ hΓ (.pair (hΓc.cons (.left _)) b (c.wk0 _))
  = .pair (hΓ.comm.s1_23_12_3 hΓc) (.let₁ (hΓ.comm.s1_23_12 hΓc).comm a b) c
  := by
  conv => rhs; rw [bind_pair_left, let_let₁]
  rw [bind_pair_left]
  induction a, b, c using quotInd₃
  apply sound; apply Wf.eqv.of_tm
  simp only [
    Wf.let₁, Wf.pair, Wf.bv0, Wf.bv1, Wf.wk0, ren_ren, <-Nat.liftWk_comp, ren,
    Nat.liftWk_comp_succ, Wf.wk1
  ]
  rfl

theorem Eqv.let₂_pair_right_wk0_wk0 {A B C D} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γr (.tensor A B)) (b : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) (c : Eqv R Γm D)
  : a.let₂ hΓ (.pair ((hΓc.cons (.left _)).cons (.left _)) b ((c.wk0 _).wk0 _))
  = .pair (hΓ.comm.s1_23_12_3 hΓc) (.let₂ (hΓ.comm.s1_23_12 hΓc).comm a b) c
  := by
  conv => rhs; rw [bind_pair_left, let_let₂]
  rw [bind_pair_left]
  induction a, b, c using quotInd₃
  apply sound; apply Wf.eqv.of_tm
  simp only [
    Wf.let₂, Wf.pair, Wf.bv0, Wf.bv1, Wf.let₁, Wf.wk0, Wf.wk1, ren_ren, <-Nat.liftWk_comp, ren,
    Nat.liftWk_comp_succ
  ]
  rfl

theorem Eqv.let₂_pair_right_bv2 {A B C} {Γ Γl Γr : Ctx? α}
  (hΓ : (Γ.cons v).SSplit (Γl.cons ⟨X, ⊤⟩) (Γr.cons w))
  (hΓc : (Γl.cons ⟨X, ⊤⟩).SSplit (Γl.cons ⟨X, 0⟩) (Γl.erase.cons ⟨X, ⊤⟩))
  (a : Eqv R (Γr.cons w) (.tensor A B)) (b : Eqv R (((Γl.cons ⟨X, 0⟩).cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  : a.let₂ hΓ
    (.pair ((hΓc.cons (.left _)).cons (.left _)) b .bv2)
  = .pair (hΓ.comm.s1_23_12_3 hΓc)
    (.let₂ (hΓ.comm.s1_23_12 hΓc).comm a b) .bv0
  := let₂_pair_right_wk0_wk0 hΓ hΓc a b (.bv0)

theorem Eqv.let_pair_right {A B C} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γm A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) B) (c : Eqv R Γr C)
  : Eqv.pair hΓ (.let₁ hΓc a b) c
  = a.let₁ (hΓ.s12_3_1_23 hΓc.comm).comm
    (.pair (hΓ.s12_3_23 hΓc.comm).left b (c.wk0 ⟨A, 0⟩))
  := by
  apply Eq.symm
  apply Eq.trans
  apply let_pair_right_wk0
  induction a, b, c using quotInd₃
  exact Eqv.of_tm rfl

theorem Eqv.let₂_pair_right {A B C D} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γm (.tensor A B)) (b : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) (c : Eqv R Γr D)
  : .pair hΓ (.let₂ hΓc a b) c
  = a.let₂ (hΓ.s12_3_1_23 hΓc.comm).comm
    (.pair (hΓ.s12_3_23 hΓc.comm).left.left b ((c.wk0 ⟨A, 0⟩).wk0 ⟨B, 0⟩))
  := by
  apply Eq.symm
  apply Eq.trans
  apply let₂_pair_right_wk0_wk0
  induction a, b, c using quotInd₃
  exact Eqv.of_tm rfl

theorem Eqv.let_pair_left_wk0 {A B C} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γr A) (b : Eqv R Γl B) (c : Eqv R (Γm.cons ⟨A, ⊤⟩) C)
  (ea eb : ε) [ha : a.HasEff ea] [hb : b.HasEff eb] (he : ea ⇌ eb)
  : a.let₁ hΓ (.pair (hΓc.cons (.right _)) (b.wk0 _) c)
  = .pair (hΓ.s12_3_1_23 hΓc) b (.let₁ (hΓ.s12_3_23 hΓc) a c)
  := by
  rw [bind_pair]
  conv => rhs; rw [bind_pair]
  rw [
    Ctx?.SSplit.comm, Var?.SSplit.comm,
    let_comm (ea := ea) (eb := eb) (ha := ha) (hb := hb) (he := he),
    wk0_let₁_right, let_let₁, wk1_pair, wk1_bv1, wk1_bv0, bind_pair_left (a := .bv2), <-wk0_bv1,
    Ctx?.SSplit.comm, Ctx?.SSplit.head, Var?.SSplit.comm,
    let_comm_pure_right (b := .bv1), bind_pair_left
  ]
  induction a, b, c using quotInd₃
  apply Eqv.of_tm
  simp [Wf.let₁, Wf.bv1, Wf.wk2, Wf.pair, Wf.wk0, ren_ren, Wf.bv0, Wf.wk1, Nat.liftWk_comp_succ]


theorem Eqv.let_pure_left_pair_wk0 {A B C} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γr A) (b : Eqv R Γl B) (c : Eqv R (Γm.cons ⟨A, ⊤⟩) C)
  [ha : a.HasEff ⊥]
  : a.let₁ hΓ (.pair (hΓc.cons (.right _)) (b.wk0 _) c)
  = .pair (hΓ.s12_3_1_23 hΓc) b (.let₁ (hΓ.s12_3_23 hΓc) a c)
  := Eqv.let_pair_left_wk0 hΓ hΓc a b c ⊥ ⊤ HasCommRel.commutes_bot_left

theorem Eqv.let_pair_pure_left_wk0 {A B C} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γr A) (b : Eqv R Γl B) (c : Eqv R (Γm.cons ⟨A, ⊤⟩) C)
  [hb : b.HasEff ⊥]
  : a.let₁ hΓ (.pair (hΓc.cons (.right _)) (b.wk0 _) c)
  = .pair (hΓ.s12_3_1_23 hΓc) b (.let₁ (hΓ.s12_3_23 hΓc) a c)
  := Eqv.let_pair_left_wk0 hΓ hΓc a b c ⊤ ⊥ HasCommRel.commutes_bot_right

theorem Eqv.let_pair_left {A B C} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γl A) (b : Eqv R Γr B) (c : Eqv R (Γm.cons ⟨B, ⊤⟩) C)
  (ea eb : ε) [ha : a.HasEff ea] [hb : b.HasEff eb] (he : ea ⇌ eb)
  : Eqv.pair hΓ a (.let₁ hΓc b c)
  = .let₁ (hΓ.comm.s12_3_1_23 hΓc.comm).comm b
    (.pair (hΓ.comm.s12_3_23 hΓc.comm).comm.right (a.wk0 ⟨B, 0⟩) c)
  := by
  rw [Eqv.let_pair_left_wk0 _ _ _ _ _ eb ea he.symm]
  induction a, b, c using quotInd₃
  apply Eqv.of_tm
  rfl

theorem Eqv.let_pair_left_pure {A B C} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γl A) (b : Eqv R Γr B) (c : Eqv R (Γm.cons ⟨B, ⊤⟩) C) [ha : a.HasEff ⊥]
  : Eqv.pair hΓ a (.let₁ hΓc b c)
  = .let₁ (hΓ.comm.s12_3_1_23 hΓc.comm).comm b
    (.pair (hΓ.comm.s12_3_23 hΓc.comm).comm.right (a.wk0 ⟨B, 0⟩) c)
  := let_pair_left hΓ hΓc a b c ⊥ ⊤ HasCommRel.commutes_bot_left

theorem Eqv.let_pure_pair_left {A B C} {Γ Γc Γl Γm Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γl A) (b : Eqv R Γr B) (c : Eqv R (Γm.cons ⟨B, ⊤⟩) C) [hb : b.HasEff ⊥]
  : Eqv.pair hΓ a (.let₁ hΓc b c)
  = .let₁ (hΓ.comm.s12_3_1_23 hΓc.comm).comm b
    (.pair (hΓ.comm.s12_3_23 hΓc.comm).comm.right (a.wk0 ⟨B, 0⟩) c)
  := let_pair_left hΓ hΓc a b c ⊤ ⊥ HasCommRel.commutes_bot_right


theorem Eqv.let_pure_pair_both {A B C D} {Γ Γl Γr Γll Γlr Γrl Γrr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) (hΓl : Γl.SSplit Γll Γlr) (hΓr : Γr.SSplit Γrl Γrr)
  (a : Eqv R Γlr A) (b : Eqv R (Γll.cons ⟨A, ⊤⟩) B)
  (c : Eqv R Γrr C) (d : Eqv R (Γrl.cons ⟨C, ⊤⟩) D)
  [hc : c.HasEff ⊥]
  : Eqv.pair hΓ (.let₁ hΓl a b) (.let₁ hΓr c d)
  = Eqv.let₂ (hΓ.s12_34_13_24 hΓl hΓr)
    (.pair (hΓ.s12_34_24 hΓl hΓr) a c)
    (.pair (hΓ.s12_34_13 hΓl hΓr).left.right (b.wk0 _) (d.wk1 _))
  := by
  rw [let_pair_right, wk0_let₁_right, let_pure_pair_left, let₂_beta]
  induction a, b, c, d using quotInd₄
  apply of_tm
  simp [Wf.let₁, Wf.pair]

theorem Eqv.let₁_pure_wk0 {Γ Γl Γr : Ctx? α} {A B}
    (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γr A) (b : Eqv R Γl B)
    [hA : IsAff A] [hΓr : Γr.del] [ha : a.HasEff ⊥]
  : a.let₁ hΓ (b.wk0 ⟨A, ⊤⟩) = b.pwk hΓ.pwk_right_del := by
  cases ha with
  | mk ha =>
  induction b using quotInd with
  | h b =>
  apply sound
  apply Wf.eqv.coh
  apply Wf.pre_beta_pureIn hΓ (ha := ha) (b := b.wk0 _) (q := .del)
  simp
  rfl
  simp [Wf.subst, Wf.pwk, Wf.wk0, <-subst_renIn]
  apply Subst.subst1_fvi
  intro x hx
  have hx := lt_of_lt_of_le hx b.deriv.fvi_le_length;
  cases x <;> simp [SubstDS.refl_get, hx]

-- theorem Eqv.let₁_wk0 {Γ Γl Γr : Ctx? α} {A B}
--     (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γr A) (b : Eqv R Γl B)
--     [hA : IsAff A] [hΓr : Γr.del] (e) [ha : a.HasEff e] [he : IsAff e]
--   : a.let₁ hΓ (b.wk0 ⟨A, ⊤⟩) = b.pwk hΓ.pwk_right_del := by
--   induction a, b using quotInd₂
--   apply sound
--   sorry
