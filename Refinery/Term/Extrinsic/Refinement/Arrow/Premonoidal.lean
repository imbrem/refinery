import Refinery.Term.Extrinsic.Refinement.Arrow.Category
import Refinery.Term.Extrinsic.Wf.DerivedRewrite
import Discretion.Premonoidal.Category

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α} [R.UWkCongr]

def DRWS.Arrow.whiskerLeft (A : R.Obj) (f : Arrow R B C) : Arrow R (A.tensor B) (A.tensor C)
  := Eqv.toArr (.letT₂ .bv0 (.pair
    ((Ctx?.erase_right _).cons (.right _))
    .bv1 (.letArrow .bv0 f)
  ))

def DRWS.Arrow.whiskerRight (f : Arrow R A B) (C : R.Obj) : Arrow R (A.tensor C) (B.tensor C)
  := Eqv.toArr (.letT₂ .bv0 (.pair
    (((Ctx?.erase_left _).cons (.left _)).cons (.right _))
     (.letArrow .bv1 f) .bv0
  ))

theorem DRWS.Obj.whiskerLeft_id (A : R.Obj) : A.id.whiskerLeft B = id (B.tensor A)
  := by simp [Arrow.whiskerLeft, Eqv.letT₂, Eqv.letArrow_id]; exact Eqv.let₂_eta _

theorem DRWS.Obj.id_whiskerRight (A : R.Obj) : A.id.whiskerRight B = id (A.tensor B)
  := by
  simp [Arrow.whiskerRight, Eqv.letArrow_id]
  convert Eqv.let₂_eta _ using 1
  apply Eqv.sound; apply Wf.eqv.of_tm; rfl

theorem Eqv.letArrow_whiskerLeft
  (a : Eqv R Γ (A.tensor B)) (f : DRWS.Arrow R B C)
  : a.letArrow (f.whiskerLeft A) = .letT₂ a (.pair
    ((Ctx?.erase_right _).cons (.right _))
    .bv1 (.letArrow .bv0 f)
  ) := by
  apply Eq.symm
  convert a.bind_let₂ _ _
  induction a, f using quotInd₂
  apply sound; apply Wf.eqv.of_tm;
  simp only [
    Wf.let₁, Wf.wk, Wf.let₂, Wf.pair, Wf.bv1, Wf.bv0, Wf.wk2, Ctx?.extend1, Ctx?.Wk.ix,
    Ctx?.Wk.drop_ix, Ctx?.length
  ]
  simp [Ctx?.nil, Ctx?.cons, Ctx?.erase, ren_ren, <-Nat.liftWk_comp]
  rfl

theorem Eqv.letArrow_whiskerRight
  (a : Eqv R Γ (A.tensor B)) (f : DRWS.Arrow R A C)
  : a.letArrow (f.whiskerRight B) = .letT₂ a (.pair
    (((Ctx?.erase_left _).cons (.left _)).cons (.right _))
     (.letArrow .bv1 f) .bv0
  ) := by
  apply Eq.symm
  convert a.bind_let₂ _ _
  induction a, f using quotInd₂
  apply sound; apply Wf.eqv.of_tm;
  simp only [
    Wf.let₁, Wf.wk, Wf.let₂, Wf.pair, Wf.bv1, Wf.bv0, Wf.wk2, Ctx?.extend1, Ctx?.Wk.ix,
    Ctx?.Wk.drop_ix, Ctx?.length
  ]
  simp [Ctx?.nil, Ctx?.cons, Ctx?.erase, ren_ren, <-Nat.liftWk_comp]
  rfl

theorem DRWS.Arrow.whiskerLeft_comp_whiskerLeft {A : R.Obj}
  (f : Arrow R B C) (g : Arrow R C D)
  : (f.whiskerLeft A).comp (g.whiskerLeft A) = (f.comp g).whiskerLeft A
  := by
  rw [
    comp, Eqv.letArrow_whiskerLeft, whiskerLeft, Eqv.toEqv_toArr, Eqv.letT₂, Eqv.letT₂,
    Eqv.let₂_let₂, whiskerLeft]
  congr 2
  conv => rhs; rw [Eqv.bind_pair]
  rw [Eqv.let₂_beta]
  congr 1
  simp only [
    Eqv.wk0_letArrow, Eqv.wk0_bv0, Eqv.let_letArrow, comp, Eqv.toArr, extend1, Eqv.wk_letArrow,
    toEqv
  ]
  congr 2
  rw [bv0_letArrow']
  conv => lhs;
  simp only [Eqv.wk2_pair, Eqv.wk1_pair, Eqv.wk1_bv1, Eqv.wk2_bv1, Eqv.wk1_bv0]
  apply Eq.symm
  generalize (Ctx?.SSplit.cons (α := α) _ _) = hΓ₁
  generalize (Ctx?.SSplit.cons (α := α) _ _) = hΓ₂
  generalize (Ctx?.SSplit.cons (α := α) _ _) = hΓ₃
  generalize hρ : (Ctx?.extend1 (hΓ := _) (α := α) _ _) = ρ
  induction f, g using Eqv.quotInd₂ with
  | h f g =>
  apply Eqv.sound
  apply ((g.wk ρ).pre_beta_pureLout hΓ₁
    (Wf.pair (.cons (.cons (.cons (Ctx?.erase_right _) (.left _)) (.left _)) (.right _))
      .bv3 .bv0) (hb := _)).coh
  rfl
  simp [
    Wf.pair, Wf.wk1, Wf.subst, Wf.wk, Wf.bv3, Wf.bv2, Wf.wk2, SubstDS.refl_get, Wf.bv0,
    Ctx?.extend1, ren_ren, <-Nat.liftWk_comp, <-hρ
  ]
  rfl
  reduce
  infer_instance

theorem DRWS.Arrow.whiskerLeft_comp {A : R.Obj} (f : Arrow R B C) (g : Arrow R C D)
  : (f.comp g).whiskerLeft A = (f.whiskerLeft A).comp (g.whiskerLeft A)
  := (f.whiskerLeft_comp_whiskerLeft g).symm

def Eqv.releft {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (.tensor .unit A)) : Eqv R Γ A
  := .letT₂ a .bv0

def Eqv.releft_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : Eqv R Γ (.tensor .unit A)
  := .pair (Ctx?.erase_left _) (.unit _) a

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

def DRWS.Obj.leftUnitor (A : R.Obj) : Arrow R (.tensor .unit A) A
  := Eqv.toArr (Eqv.bv0.releft)

def DRWS.Obj.leftUnitor_inv (A : R.Obj) : Arrow R A (.tensor .unit A)
  := Eqv.toArr (Eqv.bv0.releft_inv)

theorem Eqv.letArrow_leftUnitor {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (.tensor .unit A)) : a.letArrow (DRWS.Obj.leftUnitor A) = a.releft
  := by
  rw [releft, letT₂, bind_let₂]
  induction a using quotInd
  apply Eqv.sound; apply Wf.eqv.of_tm
  simp only [
    Wf.let₁, Wf.wk, Wf.bv0, Wf.pair, Wf.wk1, let₁.injEq, true_and, Wf.let₂, Wf.bv1,
    Ctx?.extend1, ren_ren, <-Nat.liftWk_comp
  ]
  simp [Ctx?.nil, Ctx?.cons, Ctx?.erase, ren_ren, <-Nat.liftWk_comp]
  rfl

theorem Eqv.letArrow_leftUnitor_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : a.letArrow (DRWS.Obj.leftUnitor_inv A) = a.releft_inv
  := by
  rw [releft_inv, bind_pair_right _ ⊥ ⊤]
  induction a using quotInd
  apply Eqv.sound; apply Wf.eqv.of_tm
  simp only [
    Wf.let₁, Wf.wk, Wf.bv0, Wf.pair, Wf.wk1, let₁.injEq, true_and, Wf.let₂, Wf.bv1,
    Ctx?.extend1, ren_ren, <-Nat.liftWk_comp
  ]
  simp [Ctx?.nil, Ctx?.cons, Ctx?.erase, ren_ren, <-Nat.liftWk_comp]
  rfl
  apply HasCommRel.commutes_bot_left

theorem DRWS.Obj.leftUnitor_leftUnitor_inv {A : R.Obj}
  : A.leftUnitor.comp A.leftUnitor_inv = id (.tensor .unit A) := by
  simp [DRWS.Arrow.comp, Eqv.letArrow_leftUnitor_inv, leftUnitor, Eqv.releft_releft_inv]
  rfl

theorem DRWS.Obj.leftUnitor_inv_leftUnitor {A : R.Obj}
  : A.leftUnitor_inv.comp A.leftUnitor = id A := by
  simp [DRWS.Arrow.comp, Eqv.letArrow_leftUnitor, leftUnitor_inv, Eqv.releft_inv_releft]
  rfl

def Eqv.reright {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ (A.tensor .unit)) : Eqv R Γ A
  := .letT₂ a .bv1

def Eqv.reright_inv {Γ : Ctx? α} {A : Ty α}
  (a : Eqv R Γ A) : Eqv R Γ (A.tensor .unit)
  := .pair (Ctx?.erase_right _) a (.unit _)

def DRWS.Obj.rightUnitor (A : R.Obj) : Arrow R (A.tensor .unit) A
  := Eqv.toArr (Eqv.bv0.reright)

def DRWS.Obj.rightUnitor_inv (A : R.Obj) : Arrow R A (A.tensor .unit)
  := Eqv.toArr (Eqv.bv0.reright_inv)

def Eqv.reassoc {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : Eqv R Γ (A.tensor (B.tensor C))
  := .letT₂ a (
    .let₂ ((Ctx?.erase_left _).cons (.left _)) .bv1 (.pair
      ((((Ctx?.erase_left _).cons (.right _)).cons (.left _)).cons (.right _))
      .bv1
      (.pair
        ((((Ctx?.erase_left _).cons (.right _)).cons (.left _)).cons (.left _))
        .bv0
        .bv2
      ))
  )

def Eqv.reassoc_inv {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (A.tensor (B.tensor C)))
  : Eqv R Γ ((A.tensor B).tensor C)
  := .let₂ (Ctx?.erase_left _) a (
    .let₂ ((Ctx?.erase_right _).cons (.right _)) .bv0 (.pair
      ((Ctx?.erase_right _).cons (.right _))
      (.pair
        ((((Ctx?.erase_right _).cons (.right _)).cons (.right _)).cons (.left _))
        .bv3 .bv1)
      .bv0
    ))

def Eqv.eta_assoc {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : Eqv R Γ ((A.tensor B).tensor C)
  := .letT₂ a (
    .let₂ (Ctx?.erase_left _).left .bv1 (.pair
      (Ctx?.erase_right _).right.left.left
      (.pair (Ctx?.erase_right _).right .bv1 .bv0)
      .bv2
  ))

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

def DRWS.Obj.assoc (A B C : R.Obj) : Arrow R ((A.tensor B).tensor C) (A.tensor (B.tensor C))
  := Eqv.toArr (.reassoc .bv0)

def DRWS.Obj.assoc_inv (A B C : R.Obj) : Arrow R (A.tensor (B.tensor C)) ((A.tensor B).tensor C)
  := Eqv.toArr (.reassoc_inv .bv0)

theorem Eqv.letArrow_assoc {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ ((A.tensor B).tensor C))
  : a.letArrow (DRWS.Obj.assoc A B C) = a.reassoc
  := by
  rw [reassoc, letT₂, bind_let₂]
  induction a using quotInd
  apply Eqv.sound; apply Wf.eqv.of_tm
  simp only [
    Wf.let₁, Var?.erase_erase, Wf.bv1, Wf.pair, Wf.wk, let₁.injEq, true_and, Wf.let₂, Wf.bv0,
    Wf.wk2, Wf.bv2]
  simp [ren_ren, Ctx?.extend1]

theorem Eqv.letArrow_assoc_inv {Γ : Ctx? α} {A B C : Ty α}
  (a : Eqv R Γ (A.tensor (B.tensor C)))
  : a.letArrow (DRWS.Obj.assoc_inv A B C) = a.reassoc_inv
  := by
  rw [reassoc_inv, bind_let₂]
  induction a using quotInd
  apply Eqv.sound; apply Wf.eqv.of_tm
  simp only [
    Wf.let₁, Var?.erase_erase, Wf.bv1, Wf.pair, Wf.wk, let₁.injEq, true_and, Wf.let₂, Wf.bv0,
    Wf.wk2, Wf.bv2, Wf.bv3]
  simp [ren_ren, Ctx?.extend1]

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
          (by simp; simp [quant])
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
