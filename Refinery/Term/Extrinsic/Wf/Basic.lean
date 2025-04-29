import Refinery.Term.Extrinsic.Refinement.Relation

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

structure Wf (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) : Type _ where
  tm : Term φ (Ty α)
  deriv : (Γ ⊢ tm : A)

def Deriv.wf (R : DRWS φ α) {Γ : Ctx? α} {A} {a : Term φ (Ty α)} (da : Γ ⊢ a : A) : Wf R Γ A :=
  ⟨a, da⟩

variable {R : DRWS φ α}

def Wf.wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} (a : Wf R Δ A) : Wf R Γ A
  := ⟨a.tm.ren ρ, a.deriv.wk ρ⟩

theorem Wf.tm_wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} (a : Wf R Δ A)
  : (a.wk ρ).tm = a.tm.ren ρ := rfl

def Wf.wk0 {Γ : Ctx? α} (x : Var? α) [hv : x.del] {A : Ty α} (a : Wf R Γ A) : Wf R (Γ.cons x) A
  := ⟨_, a.deriv.wk0 x⟩

def Wf.wk1 {Γ : Ctx? α} (x : Var? α) [hv : x.del] {v : Var? α} {A : Ty α} (a : Wf R (Γ.cons v) A)
  : Wf R ((Γ.cons x).cons v) A
  := ⟨_, a.deriv.wk1 x⟩

def Wf.wk2 {Γ : Ctx? α} (x : Var? α) [h : x.del] {l r : Var? α} {A : Ty α}
  (a : Wf R ((Γ.cons l).cons r) A) : Wf R (((Γ.cons x).cons l).cons r) A
  := ⟨_, a.deriv.wk2 x⟩

def Wf.pwk {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A : Ty α} (a : Wf R Δ A) : Wf R Γ A
  := ⟨a.tm, a.deriv.pwk ρ⟩

def Wf.subst {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A : Ty α} (a : Wf R Δ A) : Wf R Γ A
  := ⟨a.tm.subst σ, a.deriv.subst σ⟩

theorem Wf.tm_subst {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A : Ty α} (a : Wf R Δ A)
  : (a.subst σ).tm = a.tm.subst σ := rfl

def Wf.rby {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : Prop := R.refines.rel a.deriv b.deriv

theorem Wf.rby_refl {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A) : a.rby a
  := DRWS.uniform.refl a.deriv a.deriv

theorem Wf.rby.trans {Γ : Ctx? α} {A : Ty α} {a b c : Wf R Γ A}
  (hab : a.rby b) (hbc : b.rby c) : a.rby c
  := DRWS.uniform.trans hab hbc

theorem Wf.rby.coh_pair {Γ : Ctx? α} {A : Ty α} {a b : Term φ (Ty α)}
  {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} {da' : Γ ⊢ a : A} {db' : Γ ⊢ b : A}
  (h : rby (R := R) ⟨a, da⟩ ⟨b, db⟩) : rby (R := R) ⟨a, da'⟩ ⟨b, db'⟩
  := DRWS.rel.coh h _ _

theorem Wf.rby.coh {Γ : Ctx? α} {A : Ty α} {a b a' b' : Wf R Γ A}
  (h : a.rby b) (ha : a.tm = a'.tm) (hb : b.tm = b'.tm) : a'.rby b'
  := by cases a; cases b; cases ha; cases hb; exact h.coh_pair

instance Wf.instPreorder (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) : Preorder (Wf R Γ A) where
  le := rby
  le_refl a := a.rby_refl
  le_trans _ _ _ := rby.trans

def Wf.eqv {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : Prop := a ≤ b ∧ b ≤ a

instance Wf.setoid (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) : Setoid (Wf R Γ A) where
    r := eqv
    iseqv := {
      refl a := ⟨a.rby_refl, a.rby_refl⟩
      symm hab := ⟨hab.right, hab.left⟩
      trans hab hbc := ⟨le_trans hab.left hbc.left, le_trans hbc.right hab.right⟩
    }

theorem Wf.eqv_refl (a : Wf R Γ A) : a.eqv a := ⟨a.rby_refl, a.rby_refl⟩

theorem Wf.eqv.symm {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : a.eqv b) : b ≈ a
  := ⟨h.right, h.left⟩

theorem Wf.eqv_symm_iff {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} : a.eqv b ↔ b.eqv a
  := ⟨Wf.eqv.symm, Wf.eqv.symm⟩

theorem Wf.eqv.trans {Γ : Ctx? α} {A : Ty α} {a b c : Wf R Γ A}
  (hab : a.eqv b) (hbc : b.eqv c) : a ≈ c
  := ⟨le_trans hab.left hbc.left, le_trans hbc.right hab.right⟩

theorem Wf.eqv.coh_pair {Γ : Ctx? α} {A : Ty α} {a b : Term φ (Ty α)}
  {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} {da' : Γ ⊢ a : A} {db' : Γ ⊢ b : A}
  (h : (⟨a, da⟩ : Wf R Γ A).eqv ⟨b, db⟩) : (⟨a, da'⟩ : Wf R Γ A).eqv ⟨b, db'⟩
  := ⟨h.left.coh_pair, h.right.coh_pair⟩

theorem Wf.eqv.coh {Γ : Ctx? α} {A : Ty α} {a b a' b' : Wf R Γ A}
  (h : a.eqv b) (ha : a.tm = a'.tm) (hb : b.tm = b'.tm) : a' ≈ b'
  := ⟨h.left.coh ha hb, h.right.coh hb ha⟩

theorem Wf.eqv.coh_in {Γ : Ctx? α} {A : Ty α} {a b a' : Wf R Γ A}
  (h : a.eqv b) (ha : a.tm = a'.tm) : a' ≈ b
  := h.coh ha rfl

theorem Wf.eqv.coh_out {Γ : Ctx? α} {A : Ty α} {a b b' : Wf R Γ A}
  (h : a.eqv b) (hb : b.tm = b'.tm) : a ≈ b'
  := h.coh rfl hb

theorem Wf.eqv.of_tm {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A}
  (h : a.tm = b.tm) : a ≈ b := a.eqv_refl.coh rfl h

def Wf.bv {Γ : Ctx? α} {A : Ty α} (i : ℕ) (hv : Γ.At ⟨A, 1⟩ i) : Wf R Γ A
  := ⟨.bv i, .bv hv⟩

def Wf.bv0 {Γ : Ctx? α} [hΓ : Γ.del] {A : Ty α} {q : Quant} : Wf R (Γ.cons ⟨A, q⟩) A
  := ⟨.bv 0, .bv0⟩

def Wf.bv1 {Γ : Ctx? α} [hΓ : Γ.del] {v : Var? α} [hv : v.del] {A : Ty α} {q : Quant}
  : Wf R (((Γ.cons ⟨A, q⟩).cons v)) A := ⟨.bv 1, .bv1⟩

def Wf.bv2 {Γ : Ctx? α} [hΓ : Γ.del] {l r : Var? α} [hl : l.del] [hr : r.del] {A : Ty α}
  {q : Quant} : Wf R (((Γ.cons ⟨A, q⟩).cons l).cons r) A := ⟨.bv 2, .bv2⟩

def Wf.bv3 {Γ : Ctx? α} [hΓ : Γ.del] {l m r : Var? α} [hl : l.del] [hm : m.del] [hr : r.del]
  {A : Ty α} {q : Quant} : Wf R ((((Γ.cons ⟨A, q⟩).cons l).cons m).cons r) A := ⟨.bv 3, .bv3⟩

def Wf.op {Γ : Ctx? α} {f : φ} {A B} (hf : S.FnTy f A B) (a : Wf R Γ A) : Wf R Γ B
  := ⟨.op f a.tm, .op hf a.deriv⟩

def Wf.let₁ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Wf R Γr A) (b : Wf R (Γl.cons ⟨A, ⊤⟩) B)
  : Wf R Γ B := ⟨.let₁ a.tm A b.tm, .let₁ hΓ a.deriv b.deriv⟩

def Wf.unit (Γ : Ctx? α) [hΓ : Γ.del] : Wf R Γ Ty.unit
  := ⟨.unit, .unit hΓ⟩

def Wf.pair {Γ Γl Γr : Ctx? α}  (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Wf R Γl A) (b : Wf R Γr B) : Wf R Γ (Ty.tensor A B)
  := ⟨.pair a.tm b.tm, .pair hΓ a.deriv b.deriv⟩

def Wf.let₂ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Wf R Γr (A.tensor B)) (b : Wf R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  : Wf R Γ C := ⟨.let₂ a.tm A B b.tm, .let₂ hΓ a.deriv b.deriv⟩

def Wf.inl {Γ : Ctx? α} (A B) (a : Wf R Γ A) : Wf R Γ (Ty.coprod A B)
  := ⟨.inl A B a.tm, .inl a.deriv⟩

def Wf.inr {Γ : Ctx? α} (A B) (b : Wf R Γ B) : Wf R Γ (Ty.coprod A B)
  := ⟨.inr A B b.tm, .inr b.deriv⟩

def Wf.case {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Wf R Γr (A.coprod B)) (b : Wf R (Γl.cons ⟨A, ⊤⟩) C) (c : Wf R (Γl.cons ⟨B, ⊤⟩) C)
  : Wf R Γ C := ⟨.case a.tm A B b.tm c.tm, .case hΓ a.deriv b.deriv c.deriv⟩

def Wf.abort {Γ : Ctx? α} (A) (a : Wf R Γ Ty.empty) : Wf R Γ A
  := ⟨.abort A a.tm, .abort a.deriv⟩

def Wf.iter {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) [hc : Γl.copy] [hd : Γl.del]
  (a : Wf R Γr A) (b : Wf R (Γl.cons ⟨A, ⊤⟩) (B.coprod A))
  : Wf R Γ B := ⟨.iter a.tm A B b.tm, .iter hΓ hc hd a.deriv b.deriv⟩

theorem Wf.rby.op_congr {Γ : Ctx? α} {f : φ} {A B} (hf : S.FnTy f A B)
  {a a' : Wf R Γ A} (ha : a.rby a') : (op hf a).rby (op hf a')
  := DRWS.uniform.op hf ha

theorem Wf.rby.let₁_congr {Γ Γl Γr : Ctx? α} {A B} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γr A} {b b' : Wf R (Γl.cons ⟨A, ⊤⟩) B}
  (ha : a.rby a') (hb : b.rby b') : (let₁ hΓ a b).rby (let₁ hΓ a' b')
  := DRWS.uniform.let₁ hΓ ha hb

theorem Wf.rby.pair_congr {Γ Γl Γr : Ctx? α} {A B} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γl A} {b b' : Wf R Γr B}
  (ha : a.rby a') (hb : b.rby b') : (pair hΓ a b).rby (pair hΓ a' b')
  := DRWS.uniform.pair hΓ ha hb

theorem Wf.rby.let₂_congr {Γ Γl Γr : Ctx? α} {A B C} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γr (A.tensor B)} {b b' : Wf R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C}
  (ha : a.rby a') (hb : b.rby b') : (let₂ hΓ a b).rby (let₂ hΓ a' b')
  := DRWS.uniform.let₂ hΓ ha hb

theorem Wf.rby.inl_congr {Γ : Ctx? α} {A B} {a a' : Wf R Γ A} (ha : a.rby a')
  : (inl A B a).rby (inl A B a')
  := DRWS.uniform.inl ha

theorem Wf.rby.inr_congr {Γ : Ctx? α} {A B} {b b' : Wf R Γ B} (hb : b.rby b')
  : (inr A B b).rby (inr A B b')
  := DRWS.uniform.inr hb

theorem Wf.rby.case_congr {Γ Γl Γr : Ctx? α} {A B C} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γr (A.coprod B)} {b b' : Wf R (Γl.cons ⟨A, ⊤⟩) C} {c c' : Wf R (Γl.cons ⟨B, ⊤⟩) C}
  (ha : a.rby a') (hb : b.rby b') (hc : c.rby c') : (case hΓ a b c).rby (case hΓ a' b' c')
  := DRWS.uniform.case hΓ ha hb hc

theorem Wf.rby.abort_congr {Γ : Ctx? α} {A} {a a' : Wf R Γ Ty.empty} (ha : a.rby a')
  : (abort A a).rby (abort A a')
  := DRWS.uniform.abort ha

theorem Wf.rby.iter_congr {Γ Γl Γr : Ctx? α} {A B : Ty α} (hΓ : Γ.SSplit Γl Γr)
  [hc : Γl.copy] [hd : Γl.del]
  {a a' : Wf R Γr A} {b b' : Wf R (Γl.cons ⟨A, ⊤⟩) (B.coprod A)}
  (ha : a.rby a') (hb : b.rby b') : (iter hΓ a b).rby (iter hΓ  a' b')
  := DRWS.uniform.iter hΓ hc hd ha hb

theorem Wf.eqv.op_congr {Γ : Ctx? α} {f : φ} {A B} (hf : S.FnTy f A B)
  {a a' : Wf R Γ A} (ha : a ≈ a') : (op hf a) ≈ (op hf a')
  := ⟨rby.op_congr hf ha.left, rby.op_congr hf ha.right⟩

theorem Wf.eqv.let₁_congr {Γ Γl Γr : Ctx? α} {A B} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γr A} {b b' : Wf R (Γl.cons ⟨A, ⊤⟩) B}
  (ha : a ≈ a') (hb : b ≈ b') : (let₁ hΓ a b) ≈ (let₁ hΓ a' b')
  := ⟨rby.let₁_congr hΓ ha.left hb.left, rby.let₁_congr hΓ ha.right hb.right⟩

theorem Wf.eqv.pair_congr {Γ Γl Γr : Ctx? α} {A B} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γl A} {b b' : Wf R Γr B}
  (ha : a ≈ a') (hb : b ≈ b') : (pair hΓ a b) ≈ (pair hΓ a' b')
  := ⟨rby.pair_congr hΓ ha.left hb.left, rby.pair_congr hΓ ha.right hb.right⟩

theorem Wf.eqv.let₂_congr {Γ Γl Γr : Ctx? α} {A B C} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γr (A.tensor B)} {b b' : Wf R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C}
  (ha : a ≈ a') (hb : b ≈ b') : (let₂ hΓ a b) ≈ (let₂ hΓ a' b')
  := ⟨rby.let₂_congr hΓ ha.left hb.left, rby.let₂_congr hΓ ha.right hb.right⟩

theorem Wf.eqv.inl_congr {Γ : Ctx? α} {A B} {a a' : Wf R Γ A} (ha : a ≈ a')
  : (inl A B a) ≈ (inl A B a')
  := ⟨rby.inl_congr ha.left, rby.inl_congr ha.right⟩

theorem Wf.eqv.inr_congr {Γ : Ctx? α} {A B} {b b' : Wf R Γ B} (hb : b ≈ b')
  : (inr A B b) ≈ (inr A B b')
  := ⟨rby.inr_congr hb.left, rby.inr_congr hb.right⟩

theorem Wf.eqv.case_congr {Γ Γl Γr : Ctx? α} {A B C} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γr (A.coprod B)} {b b' : Wf R (Γl.cons ⟨A, ⊤⟩) C} {c c' : Wf R (Γl.cons ⟨B, ⊤⟩) C}
  (ha : a ≈ a') (hb : b ≈ b') (hc : c ≈ c') : (case hΓ a b c) ≈ (case hΓ a' b' c')
  := ⟨rby.case_congr hΓ ha.left hb.left hc.left, rby.case_congr hΓ ha.right hb.right hc.right⟩

theorem Wf.eqv.abort_congr {Γ : Ctx? α} {A} {a a' : Wf R Γ Ty.empty} (ha : a ≈ a')
  : (abort A a) ≈ (abort A a')
  := ⟨rby.abort_congr ha.left, rby.abort_congr ha.right⟩

theorem Wf.eqv.iter_congr {Γ Γl Γr : Ctx? α} {A B : Ty α} (hΓ : Γ.SSplit Γl Γr)
  [hc : Γl.copy] [hd : Γl.del]
  {a a' : Wf R Γr A} {b b' : Wf R (Γl.cons ⟨A, ⊤⟩) (B.coprod A)}
  (ha : a ≈ a') (hb : b ≈ b') : (iter hΓ a b) ≈ (iter hΓ a' b')
  := ⟨rby.iter_congr hΓ ha.left hb.left, rby.iter_congr hΓ ha.right hb.right⟩

def Wf.cls {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A) : Set (Term φ (Ty α))
  := {b : Term φ (Ty α) | ∃db, a ≈ ⟨b, db⟩}

theorem Wf.eqv.mem_cls {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A}
  (h : a.eqv b) : a.tm ∈ b.cls
  := ⟨a.deriv, h.symm⟩

theorem Wf.eqv.of_mem_cls {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A}
  (h : a.tm ∈ b.cls) : a ≈ b := by cases h; apply symm; apply coh_pair; assumption

theorem Wf.mem_cls_iff {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A}
  : a.tm ∈ b.cls ↔ a ≈ b := ⟨Wf.eqv.of_mem_cls, Wf.eqv.mem_cls⟩

@[simp]
theorem Wf.mem_cls {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A) : a.tm ∈ a.cls
  := a.eqv_refl.mem_cls

def Eqv (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) := Quotient (Wf.setoid R Γ A)

def Wf.e {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A) : Eqv R Γ A := ⟦a⟧

notation "e⟦" a "⟧" => Wf.e a

theorem Eqv.quotInd {Γ : Ctx? α} {A : Ty α} {motive : Eqv R Γ A → Prop} (a : Eqv R Γ A)
  (h : ∀ a : Wf R Γ A, motive e⟦a⟧) : motive a := Quotient.inductionOn a h

theorem Eqv.quotInd₂ {Γ Δ : Ctx? α} {A B : Ty α} {motive : Eqv R Γ A → Eqv R Δ B → Prop}
  (a b) (h : ∀ a b, motive e⟦a⟧ e⟦b⟧) : motive a b
  := Quotient.inductionOn₂ a b h

theorem Eqv.quotInd₃ {Γ Δ Ξ : Ctx? α} {A B C : Ty α}
  {motive : Eqv R Γ A → Eqv R Δ B → Eqv R Ξ C → Prop}
  (a b c) (h : ∀ a b c, motive e⟦a⟧ e⟦b⟧ e⟦c⟧) : motive a b c
  := Quotient.inductionOn₃ a b c h

theorem Eqv.quotInd₄ {Γ Δ Ξ Θ : Ctx? α} {A B C D : Ty α}
  {motive : Eqv R Γ A → Eqv R Δ B → Eqv R Ξ C → Eqv R Θ D → Prop}
  (a b c d) (h : ∀ a b c d, motive e⟦a⟧ e⟦b⟧ e⟦c⟧ e⟦d⟧) : motive a b c d
  := by induction a using quotInd; induction b, c, d using quotInd₃; apply h

def Eqv.liftOn {Γ : Ctx? α} {A : Ty α} {β : Type _} (a : Eqv R Γ A) (f : Wf R Γ A → β)
  (h : ∀ a b, a ≈ b → f a = f b) : β := Quotient.liftOn a f h

def Eqv.liftOn₂ {Γ Δ : Ctx? α} {A B : Ty α} {β : Type _}
  (a : Eqv R Γ A) (b : Eqv R Δ B) (f : Wf R Γ A → Wf R Δ B → β)
  (h : ∀ a b a' b', a ≈ a' → b ≈ b' → f a b = f a' b') : β := Quotient.liftOn₂ a b f h

def Eqv.liftOn₃ {Γ : Ctx? α} {A : Ty α} {B : Ty α} {C : Ty α} {β : Type _}
  (a : Eqv R Γ A) (b : Eqv R Δ B) (c : Eqv R Ξ C) (f : Wf R Γ A → Wf R Δ B → Wf R Ξ C → β)
  (h : ∀ a b c a' b' c', a ≈ a' → b ≈ b' → c ≈ c' → f a b c = f a' b' c') : β
  := a.liftOn
    (λa => b.liftOn₂ c (λb c => f a b c) (λ_ _ _ _ hb hc => h _ _ _ _ _ _ (by rfl) hb hc))
    (λa a' ha => by
      induction b, c using quotInd₂;
      simp [Eqv.liftOn₂, Wf.e]
      apply h <;> first | rfl | assumption
      )

@[simp]
theorem Eqv.liftOn_mk {Γ : Ctx? α} {A : Ty α} {β : Type _} (a : Wf R Γ A) (f : Wf R Γ A → β)
  (h) : Eqv.liftOn ⟦a⟧ f h = f a := rfl

@[simp]
theorem Eqv.liftOn₂_mk {Γ Δ : Ctx? α} {A B : Ty α} {β : Type _} (a : Wf R Γ A) (b : Wf R Δ B)
  (f : Wf R Γ A → Wf R Δ B → β) (h) : Eqv.liftOn₂ ⟦a⟧ ⟦b⟧ f h = f a b := rfl

@[simp]
theorem Eqv.liftOn₃_mk {Γ Δ Ξ : Ctx? α} {A : Ty α} {B : Ty α} {C : Ty α} {β : Type _}
  (a : Wf R Γ A) (b : Wf R Δ B) (c : Wf R Ξ C) (f : Wf R Γ A → Wf R Δ B → Wf R Ξ C → β) (h)
  : Eqv.liftOn₃ ⟦a⟧ ⟦b⟧ ⟦c⟧ f h = f a b c := rfl

def Eqv.cls {Γ : Ctx? α} {A : Ty α} (a : Eqv R Γ A) : Set (Term φ (Ty α))
  := a.liftOn Wf.cls (λ_ _ h =>
    Set.ext (λ_ => ⟨λ⟨dc, h'⟩ => ⟨dc, h.symm.trans h'⟩, λ⟨dc, h'⟩ => ⟨dc, h.trans h'⟩⟩))

def Eqv.rby {Γ : Ctx? α} {A : Ty α} (a b : Eqv R Γ A) : Prop
  := liftOn₂ a b Wf.rby (λ_ _ _ _ ha hb
    => propext ⟨λ r => ha.right.trans (r.trans hb.left), λ r => ha.left.trans (r.trans hb.right)⟩)

theorem Wf.rby_quot_iff {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : Eqv.rby ⟦a⟧ ⟦b⟧ ↔ a.rby b
  := Iff.rfl

theorem Wf.rby_mk_iff {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : e⟦a⟧.rby e⟦b⟧ ↔ a.rby b
  := Wf.rby_quot_iff a b

theorem Eqv.sound {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : a ≈ b) : e⟦a⟧ = e⟦b⟧
  := Quotient.sound h

theorem Eqv.of_tm {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : a.tm = b.tm) : e⟦a⟧ = e⟦b⟧
  := sound (Wf.eqv.of_tm h)

theorem Eqv.exact {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : e⟦a⟧ = e⟦b⟧) : a ≈ b
  := Quotient.exact h

theorem Eqv.cls_mk {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A) : e⟦a⟧.cls = a.cls
  := rfl

theorem Eqv.cls_injective {Γ : Ctx? α} {A : Ty α}
  : Function.Injective (Eqv.cls (R := R) (Γ := Γ) (A := A))
  := λa b h => by
  induction a, b using Eqv.quotInd₂; apply sound;
  rw [<-Wf.mem_cls_iff, <-Eqv.cls_mk, <-h]; apply Wf.mem_cls

theorem Eqv.cls_inj {Γ : Ctx? α} {A : Ty α} {a b : Eqv R Γ A}
  : a.cls = b.cls ↔ a = b
  := ⟨λh => Eqv.cls_injective h, λh => by cases h; rfl⟩

theorem Wf.rby.eqv {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : a.rby b) : e⟦a⟧.rby e⟦b⟧
  := h

theorem Eqv.rby.exact {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : e⟦a⟧.rby e⟦b⟧) : a.rby b
  := h

theorem Eqv.mk_eq_iff {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : e⟦a⟧ = e⟦b⟧ ↔ a ≈ b
  := ⟨exact, sound⟩

theorem Eqv.rby_refl {Γ : Ctx? α} {A : Ty α} (a : Eqv R Γ A) : a.rby a
  := by induction a using quotInd; simp [rby, Wf.rby_refl, Eqv.liftOn₂, Wf.e]

theorem Eqv.rby.trans {Γ : Ctx? α} {A : Ty α} {a b c : Eqv R Γ A} (hab : a.rby b) (hbc : b.rby c)
  : a.rby c := by induction a, b, c using quotInd₃; apply Wf.rby.trans <;> assumption

theorem Eqv.rby.antisymm {Γ : Ctx? α} {A : Ty α} {a b : Eqv R Γ A} (hab : a.rby b) (hba : b.rby a)
  : a = b := by induction a, b using Eqv.quotInd₂; exact sound ⟨hab, hba⟩

instance Eqv.instPartialOrder (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α)
  : PartialOrder (Eqv R Γ A) where
  le := rby
  le_refl a := a.rby_refl
  le_trans _ _ _ := rby.trans
  le_antisymm _ _ := rby.antisymm

def Eqv.bv {Γ : Ctx? α} {A : Ty α} (i : ℕ) (hv : Γ.At ⟨A, 1⟩ i) : Eqv R Γ A
  := e⟦Wf.bv i hv⟧

def Eqv.bv0 {Γ : Ctx? α} [hΓ : Γ.del] {A : Ty α} {q : Quant} : Eqv R (Γ.cons ⟨A, q⟩) A
  := e⟦Wf.bv0⟧

def Eqv.bv1 {Γ : Ctx? α} [hΓ : Γ.del] {v : Var? α} [hv : v.del] {A : Ty α} {q : Quant}
  : Eqv R (((Γ.cons ⟨A, q⟩).cons v)) A := e⟦Wf.bv1⟧

def Eqv.bv2 {Γ : Ctx? α} [hΓ : Γ.del] {l r : Var? α} [hl : l.del] [hr : r.del] {A : Ty α}
  {q : Quant} : Eqv R (((Γ.cons ⟨A, q⟩).cons l).cons r) A := e⟦Wf.bv2⟧

def Eqv.bv3 {Γ : Ctx? α} [hΓ : Γ.del] {l m r : Var? α} [hl : l.del] [hm : m.del] [hr : r.del]
  {A : Ty α} {q : Quant} : Eqv R ((((Γ.cons ⟨A, q⟩).cons l).cons m).cons r) A := e⟦Wf.bv3⟧

def Eqv.op {Γ : Ctx? α} {f : φ} {A B} (hf : S.FnTy f A B) (a : Eqv R Γ A) : Eqv R Γ B
  := liftOn a (λa => e⟦a.op hf⟧) (λ_ _ h => Eqv.sound <| Wf.eqv.op_congr hf h)

def Eqv.let₁ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) B)
  : Eqv R Γ B := liftOn₂ a b (λa b => e⟦a.let₁ hΓ b⟧) (λ_ _ _ _ ha hb
    => Eqv.sound <| Wf.eqv.let₁_congr hΓ ha hb)

def Eqv.unit (Γ : Ctx? α) [hΓ : Γ.del] : Eqv R Γ Ty.unit
  := e⟦Wf.unit Γ⟧

def Eqv.pair {Γ Γl Γr : Ctx? α}  (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γl A) (b : Eqv R Γr B) : Eqv R Γ (Ty.tensor A B)
  := liftOn₂ a b (λa b => e⟦a.pair hΓ b⟧) (λ_ _ _ _ ha hb
    => Eqv.sound <| Wf.eqv.pair_congr hΓ ha hb)

def Eqv.let₂ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (A.tensor B)) (b : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  : Eqv R Γ C := liftOn₂ a b (λa b => e⟦a.let₂ hΓ b⟧) (λ_ _ _ _ ha hb
    => Eqv.sound <| Wf.eqv.let₂_congr hΓ ha hb)

def Eqv.inl {Γ : Ctx? α} (A B) (a : Eqv R Γ A) : Eqv R Γ (Ty.coprod A B)
  := liftOn a (λa => e⟦a.inl A B⟧) (λ_ _ h => Eqv.sound <| Wf.eqv.inl_congr h)

def Eqv.inr {Γ : Ctx? α} (A B) (b : Eqv R Γ B) : Eqv R Γ (Ty.coprod A B)
  := liftOn b (λb => e⟦b.inr A B⟧) (λ_ _ h => Eqv.sound <| Wf.eqv.inr_congr h)

def Eqv.case {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (A.coprod B)) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) C) (c : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
  : Eqv R Γ C := liftOn₃ a b c (λa b c => e⟦a.case hΓ b c⟧)
    (λ_ _ _ _ _ _ ha hb hc => Eqv.sound <| Wf.eqv.case_congr hΓ ha hb hc)

def Eqv.abort {Γ : Ctx? α} (A) (a : Eqv R Γ Ty.empty) : Eqv R Γ A
  := liftOn a (λa => e⟦a.abort A⟧) (λ_ _ h => Eqv.sound <| Wf.eqv.abort_congr h)

def Eqv.iter {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) [hc : Γl.copy] [hd : Γl.del]
  (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) (B.coprod A))
  : Eqv R Γ B := liftOn₂ a b (λa b => e⟦a.iter hΓ b⟧) (λ_ _ _ _ ha hb
    => Eqv.sound <| Wf.eqv.iter_congr hΓ ha hb)

def Wf.castCtx {Γ Δ : Ctx? α} (hΓ : Γ = Δ) {A : Ty α} (a : Wf R Γ A) : Wf R Δ A
  := ⟨a.tm, a.deriv.cast hΓ rfl rfl⟩

@[simp] theorem Wf.castCtx_rfl {Γ : Ctx? α} {A : Ty α} (a : Wf R Γ A) : a.castCtx rfl = a := rfl

@[simp] theorem Wf.castCtx_castCtx {Γ Δ Ξ : Ctx? α}
  {A : Ty α} (hΓ : Γ = Δ) (hΔ : Δ = Ξ) (a : Wf R Γ A)
  : (a.castCtx hΓ).castCtx hΔ = a.castCtx (hΓ.trans hΔ)
  := by subst_vars; rfl

def Eqv.castCtx {Γ Δ : Ctx? α} (hΓ : Γ = Δ) {A : Ty α} (a : Eqv R Γ A) : Eqv R Δ A
  := a.liftOn (λa => e⟦a.castCtx hΓ⟧) (λ_ _ h => by cases hΓ; apply sound; exact h)

@[simp] theorem Eqv.castCtx_rfl {Γ : Ctx? α} {A : Ty α} (a : Eqv R Γ A) : a.castCtx rfl = a := by
  induction a using Eqv.quotInd; rfl

@[simp]
theorem Eqv.castCtx_castCtx {Γ Δ Ξ : Ctx? α}
  {A : Ty α} (hΓ : Γ = Δ) (hΔ : Δ = Ξ) (a : Eqv R Γ A)
  : (a.castCtx hΓ).castCtx hΔ = a.castCtx (hΓ.trans hΔ)
  := by induction a using Eqv.quotInd; subst_vars; rfl

--TODO: Wf HasEff

--TODO: Eqv term equivalence class

--TODO: Eqv HasEff (existential over equivalence class)
