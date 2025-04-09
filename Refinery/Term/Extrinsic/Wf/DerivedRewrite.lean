import Refinery.Term.Extrinsic.Wf.Rewrite
import Refinery.Term.Extrinsic.Wf.PreBeta
import Refinery.Term.Extrinsic.Wf.WkEffect

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]
          {R : DRWS φ α} [R.UWkCongr]

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

theorem Eqv.let₂_let₂ {Γ Γl Γc Γm Γr : Ctx? α} {A B C D E}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (a : Eqv R Γr (A.tensor B))
    (b : Eqv R ((Γm.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) (C.tensor D))
    (c : Eqv R ((Γl.cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩) E)
    : (a.let₂ hΓc b).let₂ hΓ c
    = a.let₂ (hΓ.s1_23_12_3 hΓc)
      (b.let₂ (((hΓ.s1_23_12 hΓc).cons (.right _)).cons (.right _)) ((c.wk2 _).wk2 _)) := by
  rw [bind_let₂, let_let₂]
  congr 1
  conv => rhs; rw [bind_let₂]
  congr 1
  induction c using quotInd
  apply sound; apply Wf.eqv.of_tm
  simp [Wf.wk1, Wf.let₂, Wf.wk2, Wf.bv0, ren_ren, <-Nat.liftWk_comp, Nat.liftWk_comp_succ]
  rfl

theorem Eqv.let₂_let₂_anti {Γ Γl Γc Γm Γr : Ctx? α} {A B C D E}
    (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
    (a : Eqv R Γr (A.tensor B))
    (b : Eqv R ((Γm.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) (C.tensor D))
    (c : Eqv R ((Γl.cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩) E)
    : a.let₂ hΓ (b.let₂ ((hΓc.cons (.right _)).cons (.right _)) ((c.wk2 _).wk2 _))
    = (a.let₂ (hΓ.s12_3_23 hΓc) b).let₂ (hΓ.s12_3_1_23 hΓc) c := by
  rw [let₂_let₂]
  induction a, b, c using quotInd₃
  apply sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.bind_pair {Γ Γl Γr : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γl A) (b : Eqv R Γr B)
  : a.pair hΓ b = .let₁ hΓ.comm a (.let₁ (Γr.erase_left.cons (.left _)) (b.wk0 _)
    (.pair (((Ctx?.erase_left _).cons (.left _)).cons (.right _)) .bv1 .bv0))
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
  : .let₁ hΓ a (.let₁ (Γl.erase_left.cons (.left _)) (b.wk0 _)
    (.pair (((Ctx?.both _).cons (.left _)).cons (.right _)) .bv1 .bv0))
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

theorem Eqv.bind_pair_right {A }{Γ Γl Γr : Ctx? α}
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
