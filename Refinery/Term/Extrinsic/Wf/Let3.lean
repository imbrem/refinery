import Refinery.Term.Extrinsic.Wf.Assoc

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

def Eqv.letr₃ {Γ Γl Γr : Ctx? α} {A B C D : Ty α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (A.tensor (B.tensor C)))
  (b : Eqv R (((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D) : Eqv R Γ D
  := .let₂ hΓ a (.let₂ Γl.erase_right.left.right .bv0 (b.wk2 _))

def Eqv.letl₃ {Γ Γl Γr : Ctx? α} {A B C D : Ty α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr ((A.tensor B).tensor C))
  (b : Eqv R (((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D) : Eqv R Γ D
  := a.reassoc.letr₃ hΓ b

theorem Eqv.letr₃_let₁ {Γ Γl Γc Γm Γr : Ctx? α} {A B C D E : Ty α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γr A) (b : Eqv R (Γm.cons ⟨A, ⊤⟩) (B.tensor (C.tensor D)))
  (c : Eqv R (((Γl.cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩) E)
  : (a.let₁ hΓc b).letr₃ hΓ c
  = a.let₁ (hΓ.s1_23_12_3 hΓc) (b.letr₃ (hΓ.s1_23_12 hΓc).right (c.wk3 ⟨A, 0⟩))
  := by
  rw [letr₃, let₂_let₁]
  congr 2
  induction c using quotInd
  apply of_tm
  simp [Wf.let₂, Wf.wk2, ren_ren, Wf.bv0, Wf.wk3]
  congr; ext x; cases x using Nat.cases2 <;> rfl

theorem Eqv.letl₃_let₁ {Γ Γl Γc Γm Γr : Ctx? α} {A B C D E : Ty α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γr A) (b : Eqv R (Γm.cons ⟨A, ⊤⟩) ((B.tensor C).tensor D))
  (c : Eqv R (((Γl.cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩) E)
  : (a.let₁ hΓc b).letl₃ hΓ c
  = a.let₁ (hΓ.s1_23_12_3 hΓc) (b.letl₃ (hΓ.s1_23_12 hΓc).right (c.wk3 ⟨A, 0⟩))
  := by rw [letl₃, let₁_reassoc, letr₃_let₁]; rfl

theorem Eqv.letr₃_let₂ {Γ Γl Γc Γm Γr : Ctx? α} {A B C D E F : Ty α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γr (A.tensor B)) (b : Eqv R ((Γm.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) (C.tensor (D.tensor E)))
  (c : Eqv R (((Γl.cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩).cons ⟨E, ⊤⟩) F)
  : (a.let₂ hΓc b).letr₃ hΓ c
  = a.let₂ (hΓ.s1_23_12_3 hΓc) (b.letr₃ (hΓ.s1_23_12 hΓc).right.right ((c.wk3 ⟨A, 0⟩).wk3 ⟨B, 0⟩))
  := by
  rw [letr₃, let₂_let₂]
  congr 2
  induction c using quotInd
  apply of_tm
  simp [Wf.let₂, Wf.wk2, ren_ren, Wf.bv0, Wf.wk3]
  congr; ext x; cases x using Nat.cases2 <;> rfl


theorem Eqv.letr₃_letT₂ {Γ Γl Γr : Ctx? α} {A B C D E F : Ty α}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (A.tensor B)) (b : Eqv R ((Γr.erase.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) (C.tensor (D.tensor E)))
  (c : Eqv R (((Γl.cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩).cons ⟨E, ⊤⟩) F)
  : (a.letT₂ b).letr₃ hΓ c
  = a.let₂ hΓ
    (b.letr₃ (Γl.erase_right.cast_right hΓ.erase_target).right.right ((c.wk3 ⟨A, 0⟩).wk3 ⟨B, 0⟩))
  := by
  rw [letT₂, letr₃_let₂]
  induction a, b, c using quotInd₃; apply of_tm; simp [Wf.wk3, Wf.wk2, Wf.let₂]

theorem Eqv.letl₃_let₂ {Γ Γl Γc Γm Γr : Ctx? α} {A B C D E F : Ty α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γr (A.tensor B)) (b : Eqv R ((Γm.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) ((C.tensor D).tensor E))
  (c : Eqv R (((Γl.cons ⟨C, ⊤⟩).cons ⟨D, ⊤⟩).cons ⟨E, ⊤⟩) F)
  : (a.let₂ hΓc b).letl₃ hΓ c
  = a.let₂ (hΓ.s1_23_12_3 hΓc) (b.letl₃ (hΓ.s1_23_12 hΓc).right.right ((c.wk3 ⟨A, 0⟩).wk3 ⟨B, 0⟩))
  := by rw [letl₃, let₂_reassoc, letr₃_let₂]; rfl

theorem Eqv.letr₃_pair {Γ Γl Γc Γm Γr : Ctx? α} {A B C D : Ty α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γm A) (b : Eqv R Γr (B.tensor C))
  (c : Eqv R (((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
  : (a.pair hΓc b).letr₃ hΓ c
  = .let₁ (hΓ.s1_23_13_2 hΓc) a
    (.let₂ (hΓ.s1_23_13 hΓc).left (b.wk0 ⟨A, 0⟩) c)
  := by
  rw [letr₃, let₂_beta]
  congr 1
  conv => rhs; rw [bind_let₂]
  rfl

theorem Eqv.letr₃_pair_anti {Γ Γl Γc Γm Γr : Ctx? α} {A B C D : Ty α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γr A) (b : Eqv R Γm (B.tensor C))
  (c : Eqv R (((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
  : Eqv.let₁ hΓ a (.let₂ hΓc.left (b.wk0 ⟨A, 0⟩) c)
  = (a.pair (hΓ.comm.s1_23_12 hΓc.comm) b).letr₃ (hΓ.comm.s1_23_12_3 hΓc.comm).comm c
  := by rw [letr₃_pair]; induction a, b, c using quotInd₃; apply of_tm; simp [Wf.let₁, Wf.let₂]

theorem Eqv.letr₃_beta {Γ Γ234 Γ34 Γ1 Γ2 Γ3 Γ4 : Ctx? α} {A B C D : Ty α}
  (hΓ : Γ.SSplit Γ1 Γ234) (hΓ234 : Γ234.SSplit Γ2 Γ34) (hΓ34 : Γ34.SSplit Γ3 Γ4)
  (a : Eqv R Γ2 A) (b : Eqv R Γ3 B) (c : Eqv R Γ4 C)
  (d : Eqv R (((Γ1.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
  : Eqv.letr₃ hΓ (.pair hΓ234 a (.pair hΓ34 b c)) d
  = .let₁ (hΓ.s1_23_13_2 hΓ234) a (.let₁
      ((hΓ.s1_23_13 hΓ234).s1_23_13_2 hΓ34).left (b.wk0 ⟨A, 0⟩)
      (.let₁
        ((hΓ.s1_23_13 hΓ234).s1_23_13 hΓ34).left.left
        ((c.wk0 ⟨A, 0⟩).wk0 ⟨B, 0⟩)
        d))
  := by rw [letr₃_pair, wk0_pair, let₂_beta]; rfl

theorem Eqv.letl₃_beta {Γ Γ234 Γ23 Γ1 Γ2 Γ3 Γ4 : Ctx? α} {A B C D : Ty α}
  (hΓ : Γ.SSplit Γ1 Γ234) (hΓ234 : Γ234.SSplit Γ23 Γ4) (hΓ23 : Γ23.SSplit Γ2 Γ3)
  (a : Eqv R Γ2 A) (b : Eqv R Γ3 B) (c : Eqv R Γ4 C)
  (d : Eqv R (((Γ1.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
  : Eqv.letl₃ hΓ (.pair hΓ234 (.pair hΓ23 a b) c) d
  = .let₁ ((hΓ.s1_23_13_2 hΓ234).s1_23_13_2 hΓ23) a
    (.let₁ ((hΓ.s1_23_13_2 hΓ234).s1_23_13 hΓ23).left (b.wk0 ⟨A, 0⟩)
      (.let₁ (hΓ.s1_23_13 hΓ234).left.left
        ((c.wk0 ⟨A, 0⟩).wk0 ⟨B, 0⟩)
        d)
    )
  := by
  rw [letl₃, reassoc_beta, letr₃_beta]
  induction a, b, c, d using quotInd₄
  apply of_tm
  rfl

theorem Eqv.letl₃_pair {Γ Γl Γc Γm Γr : Ctx? α} {A B C D : Ty α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γm (A.tensor B)) (b : Eqv R Γr C)
  (c : Eqv R (((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
  : (a.pair hΓc b).letl₃ hΓ c
  = .let₂ (hΓ.s1_23_13_2 hΓc) a
    (.let₁ (hΓ.s1_23_13 hΓc).left.left ((b.wk0 ⟨A, 0⟩).wk0 ⟨B, 0⟩) c)
  := by
  conv => lhs; rw [<-a.let₂_eta]
  rw [let₂_pair_right, letl₃_let₂, letl₃_beta, wk0_bv0]
  convert_to _ = (
    let₂ (hΓ.s1_23_13_2 hΓc) a
      (let₁
        (Ctx?.erase_right _).right.left
        bv1
        (let₁
          (Ctx?.erase_right _).right.left
          bv1
          (let₁
            (hΓ.s1_23_13 hΓc).left.left.left.left
            (wk0 { ty := B, q := 0 } (wk0 { ty := A, q := 0 } (wk0 { ty := B, q := 0 }
              (wk0 { ty := A, q := 0 } b))))
            (wk3 { ty := B, q := 0 } (wk3 { ty := A, q := 0 } c)))))
    ) using 1
  congr 1
  apply Eq.trans (swap0_swap0 _).symm
  induction a, b, c using quotInd₃
  apply of_tm
  simp [Wf.let₁, Wf.wk2, Wf.wk0, Wf.bv1, Wf.wk3, ren_ren]
  constructor
  rfl
  congr 1
  ext x; cases x using Nat.cases3 <;> rfl
  induction a, b, c using quotInd₃
  exact of_tm rfl

def Eqv.letl₃_def' {Γ Γl Γr : Ctx? α} {A B C D : Ty α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr ((A.tensor B).tensor C))
  (b : Eqv R (((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩).cons ⟨C, ⊤⟩) D)
  : a.letl₃ hΓ b = a.let₂ hΓ (.let₂ Γl.erase_right.right.left .bv1 (b.wk3 _).unswap0₂)
  := by
  rw [letl₃, reassoc, letr₃_letT₂, letr₃_let₂, letr₃_beta, wk0_bv0]
  congr 1
  convert_to (
    let₂
    Γl.erase_right.right.left
    bv1
    (let₁
      (Ctx?.erase_right _).right.left
      bv1
      (let₁
        (Ctx?.erase_right _).right.left
        bv1
        (let₁
          (Ctx?.erase_right _).right.left.left.left.left
          (wk0 { ty := B, q := 0 } (wk0 { ty := A, q := 0 } bv2))
          (wk3 { ty := B, q := 0 }
            (wk3 { ty := A, q := 0 } (wk3 { ty := C, q := 0 }
              (wk3 { ty := A.tensor B, q := 0 } b)))))))
  ) = _
  induction b using quotInd
  apply of_tm
  simp [Wf.let₂, Wf.bv1, Wf.let₁, Wf.wk0, Wf.bv2]
  congr 1
  apply Eq.trans _ (Eqv.swap0_swap0 _)
  induction b using quotInd
  apply of_tm
  simp [Wf.let₁, Wf.let₂, Wf.bv1, Wf.wk0, Wf.wk3, Wf.wk2, ren_ren, Wf.bv2]
  congr
  ext x; cases x using Nat.cases3 <;> rfl
