import Refinery.Term.Extrinsic.Wf.Wk

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α}

abbrev Wf.HasEff (a : Wf R Γ A) (e : ε) := a.tm.HasEff e

theorem Wf.HasEff.toTm {a : Wf R Γ A} {e : ε} (ha : a.HasEff e) : a.tm.HasEff e
  := ha

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

theorem Wf.HasEff.wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {a : Wf R Δ A} {e : ε} (ha : a.HasEff e)
  : (a.wk ρ).HasEff e
  := (Term.HasEff.wk_iff ρ).mpr ha

instance Wf.HasEff.instWk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {a : Wf R Δ A} (e : ε)
  [ha : a.HasEff e] : (Wf.wk ρ a).HasEff e
  := ha.wk ρ

theorem Wf.HasEff.wk0 {Γ : Ctx? α} (x : Var? α) [hx : x.del]
  (e : ε) {a : Wf R Γ A} (ha : a.HasEff e)
  : (a.wk0 x).HasEff e := by
  convert ha.wk ((Ctx?.Wk.refl Γ).skip hx) using 0
  simp [Wf.wk0, Wf.wk, Nat.stepWk, HasEff]

instance Wf.HasEff.instWk0 {Γ : Ctx? α} (x : Var? α) [hx : x.del] (e : ε) {a : Wf R Γ A}
  [ha : a.HasEff e] : (Wf.wk0 x a).HasEff e
  := ha.wk0 x

theorem Wf.HasEff.wk1 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {v : Var? α} {A : Ty α}
  (e : ε) {a : Wf R (Γ.cons v) A} (ha : a.HasEff e)
  : (a.wk1 x).HasEff e := by
  convert ha.wk (((Ctx?.Wk.refl Γ).skip hx).scons v) using 0
  simp [Wf.wk1, Wf.wk, Nat.stepWk, HasEff]

instance Wf.HasEff.instWk1 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {v : Var? α} {A : Ty α} (e : ε)
  {a : Wf R (Γ.cons v) A} [ha : a.HasEff e] : (Wf.wk1 x a).HasEff e
  := ha.wk1 x

theorem Wf.HasEff.wk2 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l r : Var? α} {A : Ty α}
  (e : ε) {a : Wf R ((Γ.cons l).cons r) A} (ha : a.HasEff e)
  : (a.wk2 x).HasEff e := by
  convert ha.wk ((((Ctx?.Wk.refl Γ).skip hx).scons l).scons r) using 0
  simp [Wf.wk2, Wf.wk, Nat.stepWk, HasEff]

instance Wf.HasEff.instWk2 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l r : Var? α} {A : Ty α} (e : ε)
  {a : Wf R ((Γ.cons l).cons r) A} [ha : a.HasEff e] : (Wf.wk2 x a).HasEff e
  := ha.wk2 x

theorem Wf.HasEff.wk3 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l m r : Var? α} {A : Ty α}
  (e : ε) {a : Wf R (((Γ.cons l).cons m).cons r) A} (ha : a.HasEff e)
  : (a.wk3 x).HasEff e := by
  convert ha.wk (((((Ctx?.Wk.refl Γ).skip hx).scons l).scons m).scons r) using 0
  simp [Wf.wk3, Wf.wk, Nat.stepWk, HasEff]

instance Wf.HasEff.instWk3 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l m r : Var? α} {A : Ty α} (e : ε)
  {a : Wf R (((Γ.cons l).cons m).cons r) A} [ha : a.HasEff e] : (Wf.wk3 x a).HasEff e
  := ha.wk3 x

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

variable [R.UWkCongr]

theorem Eqv.HasEff.wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {a : Eqv R Δ A} (e : ε) (ha : a.HasEff e)
  : Eqv.HasEff (Eqv.wk ρ a) e
  := by cases ha; constructor; apply Wf.HasEff.wk ρ; assumption

instance Eqv.HasEff.instWk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {a : Eqv R Δ A} (e : ε)
  [ha : a.HasEff e] : Eqv.HasEff (Eqv.wk ρ a) e
  := ha.wk ρ

theorem Eqv.HasEff.wk0 {Γ : Ctx? α} (x : Var? α) [hx : x.del] (e : ε)
  {a : Eqv R Γ A} (ha : a.HasEff e)
  : Eqv.HasEff (Eqv.wk0 x a) e
  := by cases ha; constructor; apply Wf.HasEff.wk0 x; assumption

instance Eqv.HasEff.instWk0 {Γ : Ctx? α} (x : Var? α) [hx : x.del] (e : ε)
  {a : Eqv R Γ A} [ha : a.HasEff e] : Eqv.HasEff (Eqv.wk0 x a) e
  := ha.wk0 x

theorem Eqv.HasEff.wk1 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {v : Var? α} {A : Ty α} (e : ε)
  {a : Eqv R (Γ.cons v) A} (ha : a.HasEff e)
  : Eqv.HasEff (Eqv.wk1 x a) e
  := by cases ha; constructor; apply Wf.HasEff.wk1 x; assumption

instance Eqv.HasEff.instWk1 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {v : Var? α} {A : Ty α} (e : ε)
  {a : Eqv R (Γ.cons v) A} [ha : a.HasEff e] : Eqv.HasEff (Eqv.wk1 x a) e
  := ha.wk1 x

theorem Eqv.HasEff.wk2 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l r : Var? α} {A : Ty α} (e : ε)
  {a : Eqv R ((Γ.cons l).cons r) A} (ha : a.HasEff e)
  : Eqv.HasEff (Eqv.wk2 x a) e
  := by cases ha; constructor; apply Wf.HasEff.wk2 x; assumption

instance Eqv.HasEff.instWk2 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l r : Var? α} {A : Ty α} (e : ε)
  {a : Eqv R ((Γ.cons l).cons r) A} [ha : a.HasEff e] : Eqv.HasEff (Eqv.wk2 x a) e
  := ha.wk2 x

theorem Eqv.HasEff.wk3 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l m r : Var? α} {A : Ty α} (e : ε)
  {a : Eqv R (((Γ.cons l).cons m).cons r) A} (ha : a.HasEff e)
  : Eqv.HasEff (Eqv.wk3 x a) e
  := by cases ha; constructor; apply Wf.HasEff.wk3 x; assumption

instance Eqv.HasEff.instWk3 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l m r : Var? α} {A : Ty α} (e : ε)
  {a : Eqv R (((Γ.cons l).cons m).cons r) A} [ha : a.HasEff e] : Eqv.HasEff (Eqv.wk3 x a) e
  := ha.wk3 x
