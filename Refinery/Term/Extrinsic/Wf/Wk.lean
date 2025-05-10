import Refinery.Term.Extrinsic.Refinement.Wk.Relation
import Refinery.Term.Extrinsic.Wf.Basic

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]
          {R : DRWS φ α} [R.UWkCongr]

theorem Wf.rby.wk_congr {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a b : Wf R Δ A} (h : a.rby b)
  : (a.wk ρ).rby (b.wk ρ) := h.dwk_congr ρ

theorem Wf.eqv.wk_congr {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a b : Wf R Δ A} (h : a.eqv b)
  : a.wk ρ ≈ b.wk ρ := ⟨h.left.wk_congr ρ, h.right.wk_congr ρ⟩

theorem Wf.eqv.wk0_congr {Γ : Ctx? α} (x : Var? α) [hx : x.del] {A : Ty α} {a b : Wf R Γ A}
  (h : a.eqv b) : a.wk0 x ≈ b.wk0 x := by
  apply Wf.eqv.coh (Wf.eqv.wk_congr (Γ.wk0 x) h) <;>
  simp [wk, wk0, Ctx?.Wk.ix, Ctx?.wk0, Nat.stepWk]

theorem Wf.eqv.wk1_congr {Γ : Ctx? α} (x : Var? α) [hx : x.del] {v : Var? α}
  {A : Ty α} {a b : Wf R (Γ.cons v) A} (h : a.eqv b) : a.wk1 x ≈ b.wk1 x := by
  apply Wf.eqv.coh (Wf.eqv.wk_congr ((Γ.wk0 x).scons _) h) <;>
  simp [wk, wk1, Ctx?.Wk.ix, Ctx?.wk0, Nat.stepWk]

theorem Wf.eqv.wk2_congr {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l r : Var? α}
  {A : Ty α} {a b : Wf R ((Γ.cons l).cons r) A} (h : a.eqv b) : a.wk2 x ≈ b.wk2 x := by
  apply Wf.eqv.coh (Wf.eqv.wk_congr (((Γ.wk0 x).scons _).scons _) h) <;>
  simp [wk, wk2, Ctx?.Wk.ix, Ctx?.wk0, Nat.stepWk]

theorem Wf.eqv.wk3_congr {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l m r : Var? α}
  {A : Ty α} {a b : Wf R (((Γ.cons l).cons m).cons r) A} (h : a.eqv b) : a.wk3 x ≈ b.wk3 x := by
  apply Wf.eqv.coh (Wf.eqv.wk_congr ((((Γ.wk0 x).scons _).scons _).scons _) h) <;>
  simp [wk, wk3, Ctx?.Wk.ix, Ctx?.wk0, Nat.stepWk]

theorem Wf.eqv.pwk_congr {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A : Ty α} {a b : Wf R Δ A} (h : a.eqv b)
  : a.pwk ρ ≈ b.pwk ρ := by
  apply Wf.eqv.coh (Wf.eqv.wk_congr ρ h) <;> simp [wk, pwk]

def Eqv.wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} (a : Eqv R Δ A) : Eqv R Γ A
  := a.liftOn (λ a => e⟦a.wk ρ⟧) (λ_ _ h => sound <| Wf.eqv.wk_congr ρ h)

theorem Eqv.wk_mk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a : Wf R Δ A}
  : Eqv.wk ρ (e⟦a⟧) = e⟦a.wk ρ⟧ := rfl

def Eqv.wk0 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {A : Ty α} (a : Eqv R Γ A) : Eqv R (Γ.cons x) A
  := a.liftOn (λ a => e⟦a.wk0 x⟧) (λ_ _ h => sound <| Wf.eqv.wk0_congr x h)

def Eqv.wk1 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {v : Var? α} {A : Ty α} (a : Eqv R (Γ.cons v) A)
  : Eqv R ((Γ.cons x).cons v) A
  := a.liftOn (λ a => e⟦a.wk1 x⟧) (λ_ _ h => sound <| Wf.eqv.wk1_congr x h)

def Eqv.wk2 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l r : Var? α} {A : Ty α}
  (a : Eqv R ((Γ.cons l).cons r) A) : Eqv R (((Γ.cons x).cons l).cons r) A
  := a.liftOn (λ a => e⟦a.wk2 x⟧) (λ_ _ h => sound <| Wf.eqv.wk2_congr x h)

def Eqv.wk3 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {l m r : Var? α} {A : Ty α}
  (a : Eqv R (((Γ.cons l).cons m).cons r) A) : Eqv R ((((Γ.cons x).cons l).cons m).cons r) A
  := a.liftOn (λ a => e⟦a.wk3 x⟧) (λ_ _ h => sound <| Wf.eqv.wk3_congr x h)

theorem Eqv.wk0_bv0 {Γ : Ctx? α} [hΓ : Γ.del] {A : Ty α} {q : Quant} {x : Var? α} [hx : x.del]
  : (Eqv.bv0 (R := R) (Γ := Γ) (A := A) (q := q)).wk0 x = .bv1
  := rfl

theorem Eqv.wk1_bv0 {Γ : Ctx? α} [hΓ : Γ.del] {A : Ty α} {q : Quant} {x : Var? α} [hx : x.del]
  : (Eqv.bv0 (R := R) (Γ := Γ) (A := A) (q := q)).wk1 x = .bv0
  := rfl

theorem Eqv.wk2_bv0 {Γ : Ctx? α} [hΓ : Γ.del] {v : Var? α} [hv : v.del]
  {A : Ty α} {q : Quant} {x : Var? α} [hx : x.del]
  : (Eqv.bv0 (R := R) (Γ := Γ.cons v) (A := A) (q := q)).wk2 x = .bv0
  := rfl

theorem Eqv.wk0_bv1 {Γ : Ctx? α} [hΓ : Γ.del] {v : Var? α} [hv : v.del]
  {A : Ty α} {q : Quant} {x : Var? α} [hx : x.del]
  : (Eqv.bv1 (R := R) (Γ := Γ) (v := v) (A := A) (q := q)).wk0 x = .bv2
  := rfl

theorem Eqv.wk1_bv1 {Γ : Ctx? α} [hΓ : Γ.del] {v : Var? α} [hv : v.del]
  {A : Ty α} {q : Quant} {x : Var? α} [hx : x.del]
  : (Eqv.bv1 (R := R) (Γ := Γ) (v := v) (A := A) (q := q)).wk1 x = .bv2
  := rfl

theorem Eqv.wk2_bv1 {Γ : Ctx? α} [hΓ : Γ.del] {v : Var? α} [hv : v.del]
  {A : Ty α} {q : Quant} {x : Var? α} [hx : x.del]
  : (Eqv.bv1 (R := R) (Γ := Γ) (v := v) (A := A) (q := q)).wk2 x = .bv1
  := rfl

theorem Eqv.wk0_bv2 {Γ : Ctx? α} [hΓ : Γ.del] {l r : Var? α} [hl : l.del] [hr : r.del]
  {A : Ty α} {q : Quant} {x : Var? α} [hx : x.del]
  : (Eqv.bv2 (R := R) (Γ := Γ) (l := l) (r := r) (A := A) (q := q)).wk0 x = .bv3
  := rfl

theorem Eqv.wk1_bv2 {Γ : Ctx? α} [hΓ : Γ.del] {l r : Var? α} [hl : l.del] [hr : r.del]
  {A : Ty α} {q : Quant} {x : Var? α} [hx : x.del]
  : (Eqv.bv2 (R := R) (Γ := Γ) (l := l) (r := r) (A := A) (q := q)).wk1 x = .bv3
  := rfl

theorem Eqv.wk2_bv2 {Γ : Ctx? α} [hΓ : Γ.del] {l r : Var? α} [hl : l.del] [hr : r.del]
  {A : Ty α} {q : Quant} {x : Var? α} [hx : x.del]
  : (Eqv.bv2 (R := R) (Γ := Γ) (l := l) (r := r) (A := A) (q := q)).wk2 x = .bv3
  := rfl

theorem Eqv.wk0_pair' {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γl A) (b : Eqv R Γr B) {x xl xr : Var? α}
  (hΓ' : (Γ.cons x).SSplit (Γl.cons xl) (Γr.cons xr)) [hx : x.del]
  : (a.pair hΓ b).wk0 x =
    haveI _ : xl.del := hΓ'.head.left_del
    haveI _ : xr.del := hΓ'.head.right_del
    (a.wk0 xl).pair hΓ' (b.wk0 xr)
  := by induction a, b using quotInd₂; apply sound; apply Wf.eqv.of_tm; rfl

theorem Eqv.wk1_pair' {Γ Γl Γr : Ctx? α} {v vl vr}
  (hΓ : (Γ.cons v).SSplit (Γl.cons vl) (Γr.cons vr)) {A B}
  (a : Eqv R (Γl.cons vl) A) (b : Eqv R (Γr.cons vr) B) {x xl xr : Var? α}
  (hΓ' : ((Γ.cons x).cons v).SSplit ((Γl.cons xl).cons vl) ((Γr.cons xr).cons vr))
  [hx : x.del]
  : (a.pair hΓ b).wk1 x =
    haveI _ : xl.del := hΓ'.tail.head.left_del
    haveI _ : xr.del := hΓ'.tail.head.right_del
    (a.wk1 xl).pair hΓ' (b.wk1 xr)
  := by induction a, b using quotInd₂; apply sound; apply Wf.eqv.of_tm; rfl

theorem Eqv.wk2_pair' {Γ Γl Γr : Ctx? α} {l r ll lr rl rr}
  (hΓ : ((Γ.cons l).cons r).SSplit ((Γl.cons ll).cons lr) ((Γr.cons rl).cons rr)) {A B}
  (a : Eqv R ((Γl.cons ll).cons lr) A) (b : Eqv R ((Γr.cons rl).cons rr) B) {x xl xr : Var? α}
  (hΓ' : (((Γ.cons x).cons l).cons r).SSplit
    (((Γl.cons xl).cons ll).cons lr)
    (((Γr.cons xr).cons rl).cons rr))
  [hx : x.del]
  : (a.pair hΓ b).wk2 x =
    haveI _ : xl.del := hΓ'.tail.tail.head.left_del
    haveI _ : xr.del := hΓ'.tail.tail.head.right_del
    (a.wk2 xl).pair hΓ' (b.wk2 xr)
  := by induction a, b using quotInd₂; apply sound; apply Wf.eqv.of_tm; rfl

theorem Eqv.wk0_pair {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γl A) (b : Eqv R Γr B) {x : Var? α} [hx : x.del]
  : (a.pair hΓ b).wk0 x = (a.wk0 x).pair (hΓ.cons (.left _)) (b.wk0 x.erase)
  := by induction a, b using quotInd₂; apply sound; apply Wf.eqv.of_tm; rfl

theorem Eqv.wk1_pair {Γ Γl Γr : Ctx? α} {v vl vr}
  (hΓ : (Γ.cons v).SSplit (Γl.cons vl) (Γr.cons vr)) {A B}
  (a : Eqv R (Γl.cons vl) A) (b : Eqv R (Γr.cons vr) B) {x : Var? α}
  [hx : x.del]
  : (a.pair hΓ b).wk1 x = (a.wk1 x).pair ((hΓ.tail.cons (.left _)).cons hΓ.head) (b.wk1 x.erase)
  := by induction a, b using quotInd₂; apply sound; apply Wf.eqv.of_tm; rfl

theorem Eqv.wk2_pair {Γ Γl Γr : Ctx? α} {l r ll lr rl rr}
  (hΓ : ((Γ.cons l).cons r).SSplit ((Γl.cons ll).cons lr) ((Γr.cons rl).cons rr)) {A B}
  (a : Eqv R ((Γl.cons ll).cons lr) A) (b : Eqv R ((Γr.cons rl).cons rr) B) {x : Var? α}
  [hx : x.del]
  : (a.pair hΓ b).wk2 x
  = (a.wk2 x).pair (((hΓ.tail.tail.cons (.left _)).cons hΓ.tail.head).cons hΓ.head) (b.wk2 x.erase)
  := by induction a, b using quotInd₂; apply sound; apply Wf.eqv.of_tm; rfl

theorem Eqv.wk_pair {Γ Δ Δl Δr : Ctx? α}
  (ρ : Γ.Wk Δ) (hΔ : Δ.SSplit Δl Δr) (a : Eqv R Δl A) (b : Eqv R Δr B)
  : (Eqv.pair hΔ a b).wk ρ = Eqv.pair (hΔ.wk ρ) (a.wk (hΔ.leftWk ρ)) (b.wk (hΔ.rightWk ρ))
  := by induction a, b using quotInd₂; apply sound; apply Wf.eqv.of_tm; simp [Wf.wk, Wf.pair]

theorem Eqv.wk_let₁ {Γ Δ Δl Δr : Ctx? α}
  (ρ : Γ.Wk Δ) (hΔ : Δ.SSplit Δl Δr) (a : Eqv R Δr A) (b : Eqv R (Δl.cons ⟨A, ⊤⟩) B)
  : (Eqv.let₁ hΔ a b).wk ρ
  = Eqv.let₁ (hΔ.wk ρ) (a.wk (hΔ.rightWk ρ)) (b.wk ((hΔ.leftWk ρ).scons _))
  := by induction a, b using quotInd₂; apply sound; apply Wf.eqv.of_tm; simp [Wf.wk, Wf.let₁]

theorem Eqv.wk_let₂ {Γ Δ Δl Δr : Ctx? α}
  (ρ : Γ.Wk Δ) (hΔ : Δ.SSplit Δl Δr)
  (a : Eqv R Δr (A.tensor B)) (b : Eqv R ((Δl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  : (Eqv.let₂ hΔ a b).wk ρ
  = Eqv.let₂ (hΔ.wk ρ) (a.wk (hΔ.rightWk ρ)) (b.wk (((hΔ.leftWk ρ).scons _).scons _))
  := by induction a, b using quotInd₂; apply sound; apply Wf.eqv.of_tm; simp [Wf.wk, Wf.let₂]

def Eqv.pwk {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A : Ty α} (a : Eqv R Δ A) : Eqv R Γ A
  := a.liftOn (λ a => e⟦a.pwk ρ⟧) (λ_ _ h => sound <| Wf.eqv.pwk_congr ρ h)

theorem Eqv.pwk_mk {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A : Ty α} {a : Wf R Δ A}
  : Eqv.pwk ρ (e⟦a⟧) = e⟦a.pwk ρ⟧ := rfl

theorem Eqv.wk0_let₁_anti {Γ Γl Γr : Ctx? α}
  (hΓ : (Γ.cons x).SSplit (Γl.cons xl) (Γr.cons xr)) {A B}
  (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) B)
  [hx : x.del] [hxl : xl.del] [hxr : xr.del]
  : (a.wk0 xr).let₁ hΓ (b.wk1 xl) = (a.let₁ hΓ.tail b).wk0 x
  := by induction a, b using quotInd₂; exact of_tm rfl

theorem Eqv.wk0_let₁_right {Γ Γl Γr : Ctx? α}
  (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) B) {x : Var? α} [hx : x.del]
  : (a.let₁ hΓ b).wk0 x = (a.wk0 x).let₁ (hΓ.right) (b.wk1 x.erase)
  := by induction a, b using quotInd₂; exact of_tm rfl

theorem Eqv.wk1_let₁_anti {Γ Γl Γr : Ctx? α}
  (hΓ : ((Γ.cons x).cons y).SSplit ((Γl.cons xl).cons yl) ((Γr.cons xr).cons yr)) {A B}
  (a : Eqv R (Γr.cons yr) A) (b : Eqv R ((Γl.cons yl).cons ⟨A, ⊤⟩) B)
  [hx : x.del] [hxl : xl.del] [hxr : xr.del]
  : (a.wk1 xr).let₁ hΓ (b.wk2 xl) = (a.let₁ (hΓ.tail.tail.cons hΓ.head) b).wk1 x
  := by induction a, b using quotInd₂; exact of_tm rfl

theorem Eqv.wk1_let₁_right {Γ Γl Γr : Ctx? α}
  (hΓ : (Γ.cons x).SSplit (Γl.cons xl) (Γr.cons xr)) {A B}
  (a : Eqv R (Γr.cons xr) A) (b : Eqv R ((Γl.cons xl).cons ⟨A, ⊤⟩) B) {y : Var? α} [hy : y.del]
  : (a.let₁ hΓ b).wk1 y = (a.wk1 y).let₁ ((hΓ.tail.cons (.right _)).cons hΓ.head) (b.wk2 y.erase)
  := by induction a, b using quotInd₂; exact of_tm rfl

theorem Eqv.pwk_wk2 {Γ Δ : Ctx? α}
  (ρ : (((Γ.cons l).cons m).cons r).PWk (((Δ.cons l').cons m').cons r'))
  {B : Ty α} [hl : l.del] [hl' : l'.del] (a : Eqv R ((Δ.cons m').cons r') B)
  : (a.wk2 l').pwk ρ = (a.pwk ((ρ.tail.tail.tail.cons ρ.tail.head).cons ρ.head)).wk2 l
  := by induction a using quotInd; exact of_tm rfl
