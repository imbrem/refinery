import Refinery.Term.Extrinsic.Wf.Rewrite
import Refinery.Term.Extrinsic.Wf.PreBeta

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]
          {R : DRWS φ α} [R.UWkCongr]

def Eqv.let₂_let₂ {Γ Γl Γc Γm Γr : Ctx? α} {A B C D E}
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

theorem Eqv.bind_pair_anti {Γ Γl Γr : Ctx? α}
    (hΓ : Γ.SSplit Γl Γr) (a : Eqv R Γr A) (b : Eqv R Γl B)
  : .let₁ hΓ a (.let₁ (Γl.erase_left.cons (.left _)) (b.wk0 _)
    (.pair (((Ctx?.both _).cons (.left _)).cons (.right _)) .bv1 .bv0))
    = a.pair hΓ.comm b
  := by rw [a.bind_pair_anti' hΓ]
