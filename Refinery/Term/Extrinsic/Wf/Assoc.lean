import Refinery.Term.Extrinsic.Wf.Swap
import Refinery.Term.Extrinsic.Wf.LetThen

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α}

def Eqv.reassoc {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : Eqv R Γ (A.tensor (B.tensor C))
  := .letT₂ a (
    .let₂ (Ctx?.erase_left _).left .bv1 (.pair
      (Ctx?.erase_left _).right.left.right
      .bv1
      (.pair
        (Ctx?.erase_left _).right.left.left
        .bv0
        .bv2
      ))
  )

instance Eqv.reassoc_effect {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C)) [a.HasEff e]
  : a.reassoc.HasEff e := by
  rw [reassoc, letT₂]
  infer_instance

def Eqv.reassoc_inv {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (A.tensor (B.tensor C)))
  : Eqv R Γ ((A.tensor B).tensor C)
  := .let₂ (Ctx?.erase_left _) a (
    .let₂ (Ctx?.erase_right _).right .bv0 (.pair
      (Ctx?.erase_right _).right
      (.pair
        (Ctx?.erase_right _).right.right.left
        .bv3 .bv1)
      .bv0
    ))

instance Eqv.reassoc_inv_effect {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (A.tensor (B.tensor C))) [a.HasEff e]
  : a.reassoc_inv.HasEff e := by
  rw [reassoc_inv]
  infer_instance

def Eqv.eta_assoc {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : Eqv R Γ ((A.tensor B).tensor C)
  := .letT₂ a (
    .let₂ (Ctx?.erase_left _).left .bv1 (.pair
      (Ctx?.erase_right _).right.left.left
      (.pair (Ctx?.erase_right _).right .bv1 .bv0)
      .bv2
  ))

def Eqv.releft {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (.tensor .unit A)) : Eqv R Γ A
  := .letT₂ a .bv0

instance Eqv.releft_effect {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (.tensor .unit A)) [a.HasEff e]
  : a.releft.HasEff e := by
  rw [releft, letT₂]
  infer_instance

def Eqv.releft_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : Eqv R Γ (.tensor .unit A)
  := .pair (Ctx?.erase_left _) (.unit _) a

instance Eqv.releft_inv_effect {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) [a.HasEff e]
  : a.releft_inv.HasEff e := by
  rw [releft_inv]
  infer_instance

def Eqv.reright {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (A.tensor .unit)) : Eqv R Γ A
  := .letT₂ a .bv1

instance Eqv.reright_effect {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (A.tensor .unit)) [a.HasEff e]
  : a.reright.HasEff e := by
  rw [reright, letT₂]
  infer_instance

def Eqv.reright_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : Eqv R Γ (A.tensor .unit)
  := .pair (Ctx?.erase_right _) a (.unit _)

instance Eqv.reright_inv_effect {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) [a.HasEff e]
  : a.reright_inv.HasEff e := by
  rw [reright_inv]
  infer_instance

variable [R.UWkCongr]

theorem Eqv.eta_assoc_eq_id {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : a.eta_assoc = a := by
  rw [Eqv.eta_assoc, letT₂]
  conv => rhs; rw [<-let₂_eta a]
  congr 1
  conv => rhs; lhs; rw [<-let₂_eta .bv1]
  rw [let₂_pair_right]
  exact Eqv.of_tm rfl

def Eqv.eta_assoc_inv {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (A.tensor (B.tensor C)))
  : Eqv R Γ (A.tensor (B.tensor C))
  := letT₂ a (
    .let₂ ((Ctx?.erase_right _).cons (.right _)) .bv0 (.pair
      (Ctx?.erase_right _).right.right
      .bv3
      (.pair (Ctx?.erase_right _).right .bv1 .bv0)
    ))

theorem Eqv.eta_assoc_inv_eq_id {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (A.tensor (B.tensor C)))
  : a.eta_assoc_inv = a := by
  rw [Eqv.eta_assoc_inv, letT₂]
  conv => rhs; rw [<-let₂_eta a]
  congr 1
  conv =>
    lhs
    rw [bind_pair_right _ ⊥ ⊤ (ha := inferInstance) (hb := inferInstance)
      (he := HasCommRel.commutes_bot_left)]
  conv =>
    rhs
    rw [
      bind_pair_right _ ⊥ ⊤ (ha := inferInstance) (hb := inferInstance)
        (he := HasCommRel.commutes_bot_left),
      <-let₂_eta .bv0, let_let₂
    ]
  exact Eqv.of_tm rfl

theorem Eqv.let₁_reassoc {Γ Γl Γr : Ctx? α} {X A B C : Ty α}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr X) (b : Eqv R (Γl.cons ⟨X, ⊤⟩) ((A.tensor B).tensor C))
  : (a.let₁ hΓ b).reassoc = a.let₁ hΓ b.reassoc
  := by
  rw [reassoc, letT₂, let₂_let₁]
  induction a, b using quotInd₂
  apply Eqv.sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.let₁_reassoc_inv {Γ Γl Γr : Ctx? α} {X A B C : Ty α}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr X) (b : Eqv R (Γl.cons ⟨X, ⊤⟩) (A.tensor (B.tensor C)))
  : (a.let₁ hΓ b).reassoc_inv = a.let₁ hΓ b.reassoc_inv
  := by
  rw [reassoc_inv, let₂_let₁]
  induction a, b using quotInd₂
  apply Eqv.sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.let₂_reassoc {Γ Γl Γr : Ctx? α} {X Y A B C : Ty α}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (X.tensor Y)) (b : Eqv R ((Γl.cons ⟨X, ⊤⟩).cons ⟨Y, ⊤⟩) ((A.tensor B).tensor C))
  : (a.let₂ hΓ b).reassoc = a.let₂ hΓ b.reassoc
  := by
  rw [reassoc, letT₂, let₂_let₂]
  induction a, b using quotInd₂
  apply Eqv.sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.let₂_reassoc_inv {Γ Γl Γr : Ctx? α} {X Y A B C : Ty α}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (X.tensor Y)) (b : Eqv R ((Γl.cons ⟨X, ⊤⟩).cons ⟨Y, ⊤⟩) (A.tensor (B.tensor C)))
  : (a.let₂ hΓ b).reassoc_inv = a.let₂ hΓ b.reassoc_inv
  := by
  rw [reassoc_inv, let₂_let₂]
  induction a, b using quotInd₂
  apply Eqv.sound; apply Wf.eqv.of_tm
  rfl

set_option maxHeartbeats 1000000000 in
theorem Eqv.reassoc_beta {Γ Γc Γl Γm Γr : Ctx? α} {A B C : Ty α}
  (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
  (a : Eqv R Γl A) (b : Eqv R Γm B) (c : Eqv R Γr C)
  : ((a.pair hΓc b).pair hΓ c).reassoc = a.pair (hΓ.s12_3_1_23 hΓc) (b.pair (hΓ.s12_3_23 hΓc) c)
  := calc
  _ = .let₁ (hΓ.s12_3_1_23 hΓc).comm a
      (.let₁ ((hΓ.s12_3_23 hΓc).comm.cons (.left _)) (b.wk0 _)
        (.let₁ ((((Ctx?.erase_left _).comm.cons (.right _))).cons (.right _))
          (.pair
            ((((Ctx?.erase_left _).comm.cons (.left _))).cons (.right _))
            .bv1 .bv0
          )
          (.let₁
            (((Ctx?.erase_right _).comm).cons (.left _)) (((c.wk0 _).wk0 _).wk0 _)
            (.let₂
              ((((Ctx?.erase_left _).comm).cons (.right _)).cons (.left _))
              .bv1
              (.pair
                ((((Ctx?.erase_right _).cons (.right _)).cons (.left _)).cons (.right _)) .bv1
                (.pair
                  ((((Ctx?.erase_right _).cons (.right _)).cons (.right _)).cons (.left _))
                  .bv0
                  .bv2
                )
              )
            )))
       ) := by
      rw [reassoc, letT₂, let₂_beta, bind_pair, let_let₁, let_let₁]
      induction a, b, c using quotInd₃
      apply Eqv.sound; apply Wf.eqv.of_tm
      simp [Wf.let₁, Wf.let₂, Wf.pair, Wf.bv1, Wf.wk1, Wf.bv0, Wf.wk0, ren_ren, <-Nat.liftWk_comp]
      constructor <;> rfl
  _ = .let₁ (hΓ.s12_3_1_23 hΓc).comm a
      (.let₁ ((hΓ.s12_3_23 hΓc).comm.cons (.left _)) (b.wk0 _)
          (.let₁
            ((((Ctx?.erase_right Γr).comm).cons (.left _)).cons (.left _)) (((c.wk0 _).wk0 _))
            (.let₂
              (((((Ctx?.erase_left _).comm).cons
                (.right ⟨A, ⊤⟩)).cons (.right ⟨B, ⊤⟩)).cons (.left ⟨C, ⊤⟩))
                (.pair
                  (((((Ctx?.erase_left _).comm.cons (.left _))).cons (.right _)).cons (.right _))
                  .bv2 .bv1
                )
              (.pair
                (((((Ctx?.erase_right _).cons
                  (.right _)).cons (.right ⟨C, ⊤⟩)).cons (.left ⟨A, ⊤⟩)).cons (.right ⟨B, ⊤⟩)) .bv1
                (.pair
                  (((((Ctx?.erase_right _).cons
                    (.right _)).cons (.right ⟨C, ⊤⟩)).cons (.left ⟨A, 0⟩)).cons (.left ⟨B, ⊤⟩))
                  .bv0
                  .bv2
                )
              )
            ))
       ) := by
        congr 2
        induction c using quotInd with
        | h c =>
        apply sound
        apply Wf.eqv.coh
        apply Wf.pre_beta_pureIn
          ((((Ctx?.erase_left _).comm.cons (.right _))).cons (.right _))
          (.pair
            ((((Ctx?.erase_left _).comm.cons (.left _))).cons (.right _))
            .bv1 .bv0
          )
          ⊤
          (by simp)
          (.let₁
            (((Ctx?.erase_right _).comm).cons (.left _)) (((c.wk0 _).wk0 _).wk0 _)
            (.let₂
              ((((Ctx?.erase_left _).comm).cons (.right _)).cons (.left _))
              .bv1
              (.pair
                ((((Ctx?.erase_right _).cons (.right _)).cons (.left _)).cons (.right _)) .bv1
                (.pair
                  ((((Ctx?.erase_right _).cons (.right _)).cons (.right _)).cons (.left _))
                  .bv0
                  .bv2
                )
              )
            ))
        rfl
        simp only [
          Wf.subst, Wf.pair, Wf.bv1, Wf.let₁, Wf.wk0, Wf.let₂, Term.subst, Wf.bv0, Wf.bv2
        ]
        simp only [EQuant.coe_top, Subst.get_lift_succ, SubstDS.subst0_get_zero, ren.eq_6, ren,
          Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, Subst.get_lift_zero, ren.eq_1, let₁.injEq,
          and_self, and_true]
        simp only [<-subst_renIn, ren_ren]
        rw [<-subst_ofRen]
        apply Subst.subst_eqOn_fvi
        intro x hx
        simp [SubstDS.refl_get, lt_of_lt_of_le hx c.deriv.fvi_le_length]
  _ = let₁ (hΓ.s12_3_1_23 hΓc).comm a
    (let₁ ((hΓ.s12_3_23 hΓc).comm.cons (Var?.SSplit.left { ty := A, q := ⊤ })) (wk0 _ b)
      (let₁
        ((Γr.erase_right.comm.cons
        (Var?.SSplit.left { ty := A, q := ⊤ })).cons (Var?.SSplit.left { ty := B, q := ⊤ }))
        (wk0 _ (wk0 _ c))
        (let₁
          ((((Γr.erase.erase_left.comm.cons (Var?.SSplit.right { ty := A, q := ⊤ })).cons
                    (Var?.SSplit.right { ty := B, q := ⊤ })).cons
                (Var?.SSplit.left { ty := C, q := ⊤ })).s1_23_13_2
            (((Γr.erase.erase.erase_left.comm.cons (Var?.SSplit.left { ty := A, q := ⊤ })).cons
                  (Var?.SSplit.right { ty := B, q := ⊤ })).cons
              (Var?.SSplit.right _)))
          bv2
          (let₁
            (((((Γr.erase.erase_left.comm.cons (Var?.SSplit.right { ty := A, q := ⊤ })).cons
                          (Var?.SSplit.right { ty := B, q := ⊤ })).cons
                      (Var?.SSplit.left { ty := C, q := ⊤ })).s1_23_13
                  (((Γr.erase.erase.erase_left.comm.cons (Var?.SSplit.left { ty := A, q := ⊤ })).cons
                        (Var?.SSplit.right { ty := B, q := ⊤ })).cons
                    (Var?.SSplit.right _))).cons
              (Var?.SSplit.left { ty := A, q := ⊤ }))
            bv2
            (pair
              (((((Γr.erase.cons _).erase_right.cons
                            (Var?.SSplit.right _)).cons
                        (Var?.SSplit.right { ty := C, q := ⊤ })).cons
                    (Var?.SSplit.left { ty := A, q := ⊤ })).cons
                (Var?.SSplit.right { ty := B, q := ⊤ }))
              bv1
              (pair
                (((((Γr.erase.cons _).erase.erase_right.cons
                              (Var?.SSplit.right _)).cons
                          (Var?.SSplit.right { ty := C, q := ⊤ })).cons
                      (Var?.SSplit.left { ty := A, q := 0 })).cons
                  (Var?.SSplit.left { ty := B, q := ⊤ }))
                bv0 bv2)))))) := by rw [let₂_beta]; rfl
    _ = let₁ (hΓ.s12_3_1_23 hΓc).comm a
    (let₁ ((hΓ.s12_3_23 hΓc).comm.cons (Var?.SSplit.left { ty := A, q := ⊤ })) (wk0 _ b)
      (let₁
        ((Γr.erase_right.comm.cons
        (Var?.SSplit.left { ty := A, q := ⊤ })).cons (Var?.SSplit.left { ty := B, q := ⊤ }))
        (wk0 _ (wk0 _ c))
        (let₁
          ((((Γr.erase.erase_left.comm.cons (Var?.SSplit.right { ty := A, q := ⊤ })).cons
                    (Var?.SSplit.right { ty := B, q := ⊤ })).cons
                (Var?.SSplit.left { ty := C, q := ⊤ })).s1_23_13_2
            (((Γr.erase.erase.erase_left.comm.cons (Var?.SSplit.left { ty := A, q := ⊤ })).cons
                  (Var?.SSplit.right { ty := B, q := ⊤ })).cons
              (Var?.SSplit.right _)))
          bv2
          (
            .pair ((Ctx?.erase_left _).cons (.left _)) .bv0
              (.pair ((((Ctx?.erase_left _).cons (.left _)).cons (.right _)).cons (.right _))
                .bv2
                .bv1)
          )
    )))
      := by
      congr 4
      apply sound
      apply Wf.eqv.coh
      apply Wf.pre_beta_pureIn
        (hΓ := (((((Γr.erase.erase_left.comm.cons (Var?.SSplit.right { ty := A, q := ⊤ })).cons
                          (Var?.SSplit.right { ty := B, q := ⊤ })).cons
                      (Var?.SSplit.left { ty := C, q := ⊤ })).s1_23_13
                  (((Γr.erase.erase.erase_left.comm.cons (Var?.SSplit.left { ty := A, q := ⊤ })).cons
                        (Var?.SSplit.right { ty := B, q := ⊤ })).cons
                    (Var?.SSplit.right _))).cons
              (Var?.SSplit.left { ty := A, q := ⊤ })))
          .bv2 ⊤ _
          (b := (.pair (((Ctx?.erase_left _).cons (.left _)).cons (.right _)) .bv1
            (.pair ((Ctx?.erase_left _).cons (.left _)) .bv0 .bv2)))
      simp; simp [quant]
      simp [Wf.let₁, Wf.pair, Wf.pwk, Wf.subst, Wf.bv1, Wf.bv2]; rfl
    _ = let₁ (hΓ.s12_3_1_23 hΓc).comm a
    (let₁ ((hΓ.s12_3_23 hΓc).comm.cons (Var?.SSplit.left { ty := A, q := ⊤ })) (wk0 _ b)
      (let₁
        ((Γr.erase_right.comm.cons
        (Var?.SSplit.left { ty := A, q := ⊤ })).cons (Var?.SSplit.left { ty := B, q := ⊤ }))
        (wk0 _ (wk0 _ c))
          (
            .pair (((Ctx?.erase_right _).cons (.right _)).cons (.right _)) .bv2
              (.pair (((Ctx?.erase_right _).cons (.left _)).cons (.right _)) .bv1 .bv0)
          )
        )) := by
      congr 3
      apply sound
      apply Wf.eqv.coh
      apply Wf.pre_beta_pureIn
        (hΓ := ((((Γr.erase.erase_left.comm.cons (Var?.SSplit.right { ty := A, q := ⊤ })).cons
                    (Var?.SSplit.right { ty := B, q := ⊤ })).cons
                (Var?.SSplit.left { ty := C, q := ⊤ })).s1_23_13_2
            (((Γr.erase.erase.erase_left.comm.cons (Var?.SSplit.left { ty := A, q := ⊤ })).cons
                  (Var?.SSplit.right { ty := B, q := ⊤ })).cons
              (Var?.SSplit.right _))))
        .bv2 ⊤ _
        (b :=
          (
            .pair ((Ctx?.erase_left _).cons (.left _)) .bv0
              (.pair ((((Ctx?.erase_left _).cons (.left _)).cons (.right _)).cons (.right _))
                .bv2
                .bv1)
          ))
      simp; simp [quant]
      simp [Wf.let₁, Wf.pair, Wf.pwk, Wf.subst]; rfl
  _ = _ :=  by
    conv => rhs; rw [bind_pair]; rhs; lhs; rw [wk0_pair, bind_pair]
    rw [bind_pair_right _ ⊥ ⊤, let_let₁, let_let₁]
    congr 1
    induction b, c using quotInd₂
    apply sound; apply Wf.eqv.of_tm
    simp [Wf.let₁, Wf.wk0, Wf.pair, Wf.bv0, Wf.wk1, Wf.bv2, Wf.bv1]
    apply HasCommRel.commutes_bot_left

theorem Eqv.reassoc_reassoc_inv {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (A.tensor (B.tensor C)))
  : a.reassoc_inv.reassoc = a
  := calc
  _ = a.eta_assoc_inv := by
    rw [reassoc_inv, let₂_reassoc, let₂_reassoc, reassoc_beta]
    induction a using quotInd
    exact Eqv.of_tm rfl
  _ = _ := by rw [a.eta_assoc_inv_eq_id]

theorem Eqv.reassoc_inv_injective {Γ : Ctx? α} {A B C : Ty α}
  (a b : Eqv R Γ (A.tensor (B.tensor C)))
  (h : a.reassoc_inv = b.reassoc_inv) : a = b
  := by rw [<-a.reassoc_reassoc_inv, <-b.reassoc_reassoc_inv, h]

theorem Eqv.reassoc_inv_reassoc {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : a.reassoc.reassoc_inv = a
  := by calc
  _ = a.eta_assoc := by
    rw [eta_assoc, reassoc, letT₂, let₂_reassoc_inv, let₂_reassoc_inv]
    congr 2
    rw [
      reassoc_inv, let₂_beta, wk0_pair, wk0_bv0, wk0_bv2,
      let₂_let₁_bv0_anti'
        (c' :=
          (.pair (Ctx?.erase_right _).right (.pair (Ctx?.erase_right _).right.right .bv2 .bv1) .bv0)
        )
        (hc := by apply Eqv.of_tm; simp [Wf.pair, Wf.wk2, Wf.bv1, Wf.bv0, Wf.bv2, Wf.bv3]),
      let₂_beta
    ]
    conv => rhs; lhs; rw [bind_pair]
    rw [let_pair_right, let_pair_right]
    conv => rhs; rhs; rhs; rw [
      bind_pair_right _ ⊥ ⊤ (ha := inferInstance) (hb := inferInstance)
        (he := HasCommRel.commutes_bot_left),
    ]
    apply Eqv.of_tm
    simp [Wf.let₁, Wf.bv1, Wf.wk0, Wf.bv0, Wf.bv2, Wf.bv3, Wf.pwk, Wf.pair]
  _ = _ := by rw [a.eta_assoc_eq_id]

theorem Eqv.reassoc_injective {Γ : Ctx? α} {A B C : Ty α}
  (a b : Eqv R Γ ((A.tensor B).tensor C))
  (h : a.reassoc = b.reassoc) : a = b
  := by rw [<-a.reassoc_inv_reassoc, <-b.reassoc_inv_reassoc, h]

theorem Eqv.reassoc_inv_beta {Γ Γc Γl Γm Γr : Ctx? α} {A B C : Ty α}
  (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
  (a : Eqv R Γl A) (b : Eqv R Γm B) (c : Eqv R Γr C)
  : (a.pair hΓ (b.pair hΓc c)).reassoc_inv = (a.pair (hΓ.s1_23_12 hΓc) b).pair (hΓ.s1_23_12_3 hΓc) c
  := by
  apply reassoc_injective
  rw [reassoc_reassoc_inv, reassoc_beta]
  induction a, b, c using quotInd₃
  exact Eqv.of_tm rfl

theorem Eqv.releft_inv_releft {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : a.releft_inv.releft = a := by
  rw [releft_inv, releft, letT₂, let₂_beta]
  conv => rhs; rw [<-let₁_eta a, let₁_unit_anti (let₁ _ _ _)]
  induction a using quotInd
  apply Eqv.sound; apply Wf.eqv.of_tm
  rfl

theorem Eqv.releft_releft_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (.tensor .unit A)) : a.releft.releft_inv = a := by
  rw [releft, releft_inv]
  conv => rhs; rw [<-letT₂_eta a]; rhs; lhs; rw [bv1.unit_pure_del (hΓ := by
    rw [Ctx?.cons_del_iff]
    constructor
    rw [Ctx?.cons_del_iff]
    constructor
    infer_instance
    apply Var?.del.instTopQuant
    infer_instance
  )]
  rw [bind_pair_right _ ⊥ ⊤, letT₂, let_let₂, letT₂]
  conv => rhs; rhs; rw [<-let₁_bv0 (.pair _ _ _)]
  induction a using quotInd
  apply Eqv.sound; apply Wf.eqv.of_tm
  rfl
  apply HasCommRel.commutes_bot_left

theorem Eqv.reright_reright_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : a.reright_inv.reright = a := by
  rw [reright_inv, reright, letT₂, let₂_beta]
  conv => rhs; rw [<-let₁_eta a, let₁_unit_anti .bv0]
  induction a using quotInd
  exact Eqv.of_tm rfl

theorem Eqv.reright_inv_reright {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (A.tensor .unit)) : a.reright.reright_inv = a := by
  rw [reright, reright_inv, letT₂, let₂_pair_right]
  conv => rhs; rw [<-a.let₂_eta]
  rw [bv0.unit_pure_del]
  induction a using quotInd
  exact Eqv.of_tm rfl

theorem Eqv.reassoc_let₂ {Γ Γl Γr : Ctx? α} {A B C D : Ty α}
  (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr ((A.tensor B).tensor C)) (b : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B.tensor C, ⊤⟩) D)
  : a.reassoc.let₂ hΓ b
  = a.let₂ hΓ (
    .let₂ Γl.erase_right.right.left .bv1 (
    .let₁ Γl.erase_right.left.right.left.right (.pair (Ctx?.erase_left _).left .bv0 .bv2)
    (((b.wk2 ⟨A.tensor B, 0⟩).wk2 ⟨C, 0⟩).wk1 ⟨B, 0⟩)
  ))
  := by
  rw [reassoc, letT₂, let₂_let₂_erase]
  congr 1
  rw [let₂_let₂]
  convert_to (let₂ Γl.erase_right.right.left
    bv1
    (let₂
      Γl.erase_right.right.right.right.right
      (pair (Ctx?.erase_left _).left.right bv1
        (pair (Ctx?.erase_left _).right.left bv0 bv2))
      (wk2 { ty := B, q := 0 }
        (wk2 { ty := A, q := 0 } (wk2 { ty := C, q := 0 } (wk2 { ty := A.tensor B, q := 0 } b))))))
        = _
  induction b using quotInd; apply Eqv.of_tm; simp [Wf.let₂, Wf.pair, Wf.bv0, Wf.bv1, Wf.bv2]
  congr 1
  rw [let₂_beta]
  induction b using quotInd with
  | h b =>
  apply sound
  apply Wf.eqv.coh_out
  apply Wf.pre_beta_pureIIn
  simp
  simp [Wf.subst, Wf.let₁, Wf.pair, Wf.wk0, Wf.bv0, Wf.bv1, Wf.bv2, Wf.wk1, Wf.wk2, <-subst_renIn]
  rw [ren_ren, ren_ren, <-subst_ofRen]
  constructor
  constructor
  rfl
  rfl
  apply Subst.subst_eqOn_fvi
  intro x hx
  simp only [Subst.get_renIn, Subst.get_ofRen, Function.comp_apply]
  cases x using Nat.cases2 with
  | rest x =>
    simp [SubstDS.refl_get, Ctx?.SSplit.c1_23_13, Ctx?.SSplit.l12_3_1_23]
    rw [ite_cond_eq_true]
    rfl
    have hx : x + 2 < Γl.length + 2 := lt_of_lt_of_le hx b.deriv.fvi_le_length
    simp
    omega
  | _ => rfl

theorem Eqv.reassoc_letT₂ {Γ : Ctx? α} {A B C D : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C)) (b : Eqv R ((Γ.erase.cons ⟨A, ⊤⟩).cons ⟨B.tensor C, ⊤⟩) D)
  : a.reassoc.letT₂ b
  = a.letT₂ (
    .let₂ (Ctx?.erase_right _).right.left .bv1 (
    .let₁ (Ctx?.erase_right _).right.left.right (.pair (Ctx?.erase_left _).left .bv0 .bv2)
    (((b.wk2 ⟨A.tensor B, 0⟩).wk2 ⟨C, 0⟩).wk1 ⟨B, 0⟩)
  ))
  := by rw [letT₂, reassoc_let₂]; rfl

theorem Eqv.wk0_reassoc {Γ : Ctx? α} {A B C : Ty α} {x : Var? α} [hx : x.del]
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : a.reassoc.wk0 x = (a.wk0 x).reassoc := by induction a using quotInd; exact Eqv.of_tm rfl

theorem Eqv.wk0_reassoc_inv {Γ : Ctx? α} {A B C : Ty α} {x : Var? α} [hx : x.del]
  (a : Eqv R Γ (A.tensor (B.tensor C)))
  : a.reassoc_inv.wk0 x = (a.wk0 x).reassoc_inv := by induction a using quotInd; exact Eqv.of_tm rfl

theorem Eqv.wk0_releft {Γ : Ctx? α} {A : Ty α} {x : Var? α} [hx : x.del]
  (a : Eqv R Γ (.tensor .unit A))
  : a.releft.wk0 x = (a.wk0 x).releft := by induction a using quotInd; exact Eqv.of_tm rfl

theorem Eqv.wk0_reright {Γ : Ctx? α} {A : Ty α} {x : Var? α} [hx : x.del]
  (a : Eqv R Γ (A.tensor .unit))
  : a.reright.wk0 x = (a.wk0 x).reright := by induction a using quotInd; exact Eqv.of_tm rfl

theorem Eqv.wk0_releft_inv {Γ : Ctx? α} {A : Ty α} {x : Var? α} [hx : x.del]
  (a : Eqv R Γ A)
  : a.releft_inv.wk0 x = (a.wk0 x).releft_inv := by induction a using quotInd; exact Eqv.of_tm rfl

theorem Eqv.wk0_reright_inv {Γ : Ctx? α} {A : Ty α} {x : Var? α} [hx : x.del]
  (a : Eqv R Γ A)
  : a.reright_inv.wk0 x = (a.wk0 x).reright_inv := by induction a using quotInd; exact Eqv.of_tm rfl
