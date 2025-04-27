import Refinery.Term.Extrinsic.Wf.Basic

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α}

abbrev Wf.HasEff (a : Wf R Γ A) (e : ε) := a.tm.HasEff e

instance Wf.HasEff.top {a : Wf R Γ A} : a.HasEff ⊤
  := Term.HasEff.top

@[simp]
instance Wf.HasEff.bv {Γ : Ctx? α} {A : Ty α} (e : ε) (i) (hv : Γ.At ⟨A, 1⟩ i)
  : (Wf.bv (R := R) i hv).HasEff e
  := Term.HasEff.bv i

@[simp]
instance Wf.HasEff.bv0 {Γ : Ctx? α} [hΓ : Γ.del] (e : ε)
  : (Wf.bv0 (R := R) (Γ := Γ) (hΓ := hΓ) (q := q) (A := A)).HasEff e
  := Term.HasEff.bv 0

@[simp]
instance Wf.HasEff.bv1 {Γ : Ctx? α} [hΓ : Γ.del] (e : ε) {v : Var? α} [hv : v.del]
  : (Wf.bv1 (R := R) (Γ := Γ) (hΓ := hΓ) (v := v) (hv := hv) (q := q) (A := A)).HasEff e
  := Term.HasEff.bv 1

@[simp]
instance Wf.HasEff.bv2 {Γ : Ctx? α} [hΓ : Γ.del] (e : ε) {l r : Var? α}
  [hl : l.del] [hr : r.del]
  : (
      Wf.bv2 (R := R) (Γ := Γ) (hΓ := hΓ) (l := l) (hl := hl) (r := r) (hr := hr) (q := q) (A := A)
    ).HasEff e
  := Term.HasEff.bv 2

@[simp]
instance Wf.HasEff.bv3 {Γ : Ctx? α} [hΓ : Γ.del] (e : ε) {l m r : Var? α}
  [hl : l.del] [hm : m.del] [hr : r.del]
  : (
      Wf.bv3 (R := R) (Γ := Γ) (hΓ := hΓ)
        (l := l) (hl := hl) (m := m) (hm := hm) (r := r) (hr := hr)
        (q := q) (A := A)
    ).HasEff e
  := Term.HasEff.bv 3

theorem Wf.HasEff.pair {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  {a : Wf R Γl A} {b : Wf R Γr B} {e : ε}
  (ha : a.HasEff e) (hb : b.HasEff e) : (pair hΓ a b).HasEff e
  := Term.HasEff.pair ha hb

instance Wf.HasEff.instPair {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  (a : Wf R Γl A) (b : Wf R Γr B) (e : ε)
  [ha : a.HasEff e] [hb : b.HasEff e] : (Wf.pair hΓ a b).HasEff e
  := ha.pair hΓ hb

theorem Wf.HasEff.let₁ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  {a : Wf R Γr A} {b : Wf R (Γl.cons ⟨A, ⊤⟩) B} {e : ε}
  (ha : a.HasEff e) (hb : b.HasEff e) : (a.let₁ hΓ b).HasEff e
  := Term.HasEff.let₁ ha hb

instance Wf.HasEff.instLet₁ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  (a : Wf R Γr A) (b : Wf R (Γl.cons ⟨A, ⊤⟩) B) (e : ε)
  [ha : a.HasEff e] [hb : b.HasEff e] : (Wf.let₁ hΓ a b).HasEff e
  := ha.let₁ hΓ hb

theorem Wf.HasEff.let₂ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B C : Ty α}
  {a : Wf R Γr (A.tensor B)} {b : Wf R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C} {e : ε}
  (ha : a.HasEff e) (hb : b.HasEff e) : (a.let₂ hΓ b).HasEff e
  := Term.HasEff.let₂ ha hb

instance Wf.HasEff.instLet₂ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B C : Ty α}
  (a : Wf R Γr (A.tensor B)) (b : Wf R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) (e : ε)
  [ha : a.HasEff e] [hb : b.HasEff e] : (Wf.let₂ hΓ a b).HasEff e
  := ha.let₂ hΓ hb

set_option linter.unusedVariables false in
instance Wf.HasEff.unit {Γ : Ctx? α} [hΓ : Γ.del] (e : ε) : (unit Γ).HasEff (R := R) e
  := Term.HasEff.unit

theorem Wf.HasEff.case {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B C : Ty α}
  {a : Wf R Γr (A.coprod B)} {b : Wf R (Γl.cons ⟨A, ⊤⟩) C}
  {c : Wf R (Γl.cons ⟨B, ⊤⟩) C} {e : ε}
  (ha : a.HasEff e) (hb : b.HasEff e) (hc : c.HasEff e)
  : (a.case hΓ b c).HasEff e
  := Term.HasEff.case ha hb hc

instance Wf.HasEff.instCase {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B C : Ty α}
  (a : Wf R Γr (A.coprod B)) (b : Wf R (Γl.cons ⟨A, ⊤⟩) C)
  (c : Wf R (Γl.cons ⟨B, ⊤⟩) C) (e : ε)
  [ha : a.HasEff e] [hb : b.HasEff e] [hc : c.HasEff e] : (Wf.case hΓ a b c).HasEff e
  := ha.case hΓ hb hc

theorem Wf.HasEff.iter {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  {a : Wf R Γr A} {b : Wf R (Γl.cons ⟨A, ⊤⟩) (B.coprod A)} {e : ε}
  (he : e ∈ S.iterative) (hc : Γl.copy) (hd : Γl.del)
  (ha : a.HasEff e) (hb : b.HasEff e) : (a.iter (hc := hc) (hd := hd) hΓ b).HasEff e
  := Term.HasEff.iter he ha hb

instance Wf.HasEff.instIter {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  (a : Wf R Γr A) (b : Wf R (Γl.cons ⟨A, ⊤⟩) (B.coprod A)) (e : ε)
  (he : e ∈ S.iterative) (hc : Γl.copy) (hd : Γl.del)
  [ha : a.HasEff e] [hb : b.HasEff e] : (Wf.iter hΓ a b).HasEff e
  := ha.iter hΓ he hc hd hb

inductive Eqv.HasEff {Γ : Ctx? α} {A : Ty α} : Eqv R Γ A → ε → Prop
  | mk {a : Wf R Γ A} (ha : a.HasEff e) : Eqv.HasEff e⟦a⟧ e

attribute [class] Eqv.HasEff

attribute [instance] Eqv.HasEff.mk

instance Eqv.HasEff.top {a : Eqv R Γ A} : a.HasEff ⊤
  := by induction a using quotInd; constructor; infer_instance

instance Eqv.HasEff.bv {Γ : Ctx? α} {A : Ty α} (e : ε) (i) (hv : Γ.At ⟨A, 1⟩ i)
  : Eqv.HasEff (Eqv.bv (R := R) i hv) e := .mk (.bv e i hv)

instance Eqv.HasEff.bv0 {Γ : Ctx? α} [hΓ : Γ.del] (e : ε)
  : Eqv.HasEff (Eqv.bv0 (R := R) (Γ := Γ) (hΓ := hΓ) (q := q) (A := A)) e
  := .mk (.bv0 e)

instance Eqv.HasEff.bv1 {Γ : Ctx? α} [hΓ : Γ.del] (e : ε) {v : Var? α} [hv : v.del]
  : Eqv.HasEff (Eqv.bv1 (R := R) (Γ := Γ) (hΓ := hΓ) (v := v) (hv := hv) (q := q) (A := A)) e
  := .mk (.bv1 e)

instance Eqv.HasEff.bv2 {Γ : Ctx? α} [hΓ : Γ.del] (e : ε) {l r : Var? α}
  [hl : l.del] [hr : r.del]
  : Eqv.HasEff (
    Eqv.bv2 (R := R) (Γ := Γ) (hΓ := hΓ) (l := l) (hl := hl) (r := r) (hr := hr) (q := q) (A := A)
  ) e
  := .mk (.bv2 e)

instance Eqv.HasEff.bv3 {Γ : Ctx? α} [hΓ : Γ.del] (e : ε) {l m r : Var? α}
  [hl : l.del] [hm : m.del] [hr : r.del]
  : Eqv.HasEff (
    Eqv.bv3 (R := R) (Γ := Γ) (hΓ := hΓ)
      (l := l) (hl := hl) (m := m) (hm := hm) (r := r) (hr := hr)
      (q := q) (A := A)
  ) e
  := .mk (.bv3 e)

theorem Eqv.HasEff.pair {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  {a : Eqv R Γl A} {b : Eqv R Γr B} (e : ε)
  (ha : a.HasEff e) (hb : b.HasEff e) : Eqv.HasEff (Eqv.pair hΓ a b) e
  := by cases ha; cases hb; constructor; infer_instance

instance Eqv.HasEff.instPair {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  (a : Eqv R Γl A) (b : Eqv R Γr B) (e : ε)
  [ha : a.HasEff e] [hb : b.HasEff e] : Eqv.HasEff (Eqv.pair hΓ a b) e
  := ha.pair hΓ _ hb

instance Eqv.HasEff.unit {Γ : Ctx? α} [hΓ : Γ.del] (e : ε)
  : Eqv.HasEff (R := R) (Eqv.unit Γ) e
  := .mk (.unit e)

theorem Eqv.HasEff.let₁ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  {a : Eqv R Γr A} {b : Eqv R (Γl.cons ⟨A, ⊤⟩) B} (e : ε)
  (ha : a.HasEff e) (hb : b.HasEff e) : Eqv.HasEff (Eqv.let₁ hΓ a b) e
  := by cases ha; cases hb; constructor; infer_instance

instance Eqv.HasEff.instLet₁ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) B) (e : ε)
  [ha : a.HasEff e] [hb : b.HasEff e] : Eqv.HasEff (Eqv.let₁ hΓ a b) e
  := ha.let₁ hΓ _ hb

theorem Eqv.HasEff.let₂ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B C : Ty α}
  {a : Eqv R Γr (A.tensor B)} {b : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C} (e : ε)
  (ha : a.HasEff e) (hb : b.HasEff e) : Eqv.HasEff (Eqv.let₂ hΓ a b) e
  := by cases ha; cases hb; constructor; infer_instance

instance Eqv.HasEff.instLet₂ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B C : Ty α}
  (a : Eqv R Γr (A.tensor B)) (b : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C) (e : ε)
  [ha : a.HasEff e] [hb : b.HasEff e] : Eqv.HasEff (Eqv.let₂ hΓ a b) e
  := ha.let₂ hΓ _ hb

theorem Eqv.HasEff.case {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B C : Ty α}
  {a : Eqv R Γr (A.coprod B)} {b : Eqv R (Γl.cons ⟨A, ⊤⟩) C}
  {c : Eqv R (Γl.cons ⟨B, ⊤⟩) C} (e : ε)
  (ha : a.HasEff e) (hb : b.HasEff e) (hc : c.HasEff e)
  : Eqv.HasEff (Eqv.case hΓ a b c) e
  := by cases ha; cases hb; cases hc; constructor; infer_instance

instance Eqv.HasEff.instCase {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B C : Ty α}
  (a : Eqv R Γr (A.coprod B)) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) C)
  (c : Eqv R (Γl.cons ⟨B, ⊤⟩) C) (e : ε)
  [ha : a.HasEff e] [hb : b.HasEff e] [hc : c.HasEff e] : Eqv.HasEff (Eqv.case hΓ a b c) e
  := ha.case hΓ _ hb hc

theorem Eqv.HasEff.iter {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) {A B : Ty α}
  {a : Eqv R Γr A} {b : Eqv R (Γl.cons ⟨A, ⊤⟩) (B.coprod A)} (e : ε)
  (he : e ∈ S.iterative) (hc : Γl.copy) (hd : Γl.del)
  (ha : a.HasEff e) (hb : b.HasEff e) : Eqv.HasEff (Eqv.iter hΓ a b) e
  := by cases ha; cases hb; constructor; apply Wf.HasEff.iter <;> assumption
