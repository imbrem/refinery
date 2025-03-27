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

instance Wf.instPreorder (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) : Preorder (Wf R Γ A) where
  le := rby
  le_refl a := a.rby_refl
  le_trans _ _ _ := rby.trans

instance Wf.setoid (R : DRWS φ α) (Γ : Ctx? α) (A : Ty α) : Setoid (Wf R Γ A) where
    r l r := l ≤ r ∧ r ≤ l
    iseqv := {
      refl a := ⟨le_refl a, le_refl a⟩
      symm hab := ⟨hab.right, hab.left⟩
      trans hab hbc := ⟨le_trans hab.left hbc.left, le_trans hbc.right hab.right⟩
    }

def Wf.bv {Γ : Ctx? α} {A : Ty α} (i : ℕ) (hv : Γ.At ⟨A, 1⟩ i) : Wf R Γ A
  := ⟨.bv i, .bv hv⟩

def Wf.bv0 {Γ : Ctx? α} [hΓ : Γ.del] {A : Ty α} {q : Quant} : Wf R (Γ.cons ⟨A, q⟩) A
  := ⟨.bv 0, .bv0⟩

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

theorem Wf.equiv_op_congr {Γ : Ctx? α} {f : φ} {A B} (hf : S.FnTy f A B)
  {a a' : Wf R Γ A} (ha : a ≈ a') : (op hf a) ≈ (op hf a')
  := ⟨rby.op_congr hf ha.left, rby.op_congr hf ha.right⟩

theorem Wf.equiv_let₁_congr {Γ Γl Γr : Ctx? α} {A B} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γr A} {b b' : Wf R (Γl.cons ⟨A, ⊤⟩) B}
  (ha : a ≈ a') (hb : b ≈ b') : (let₁ hΓ a b) ≈ (let₁ hΓ a' b')
  := ⟨rby.let₁_congr hΓ ha.left hb.left, rby.let₁_congr hΓ ha.right hb.right⟩

theorem Wf.equiv_pair_congr {Γ Γl Γr : Ctx? α} {A B} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γl A} {b b' : Wf R Γr B}
  (ha : a ≈ a') (hb : b ≈ b') : (pair hΓ a b) ≈ (pair hΓ a' b')
  := ⟨rby.pair_congr hΓ ha.left hb.left, rby.pair_congr hΓ ha.right hb.right⟩

theorem Wf.equiv_let₂_congr {Γ Γl Γr : Ctx? α} {A B C} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γr (A.tensor B)} {b b' : Wf R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C}
  (ha : a ≈ a') (hb : b ≈ b') : (let₂ hΓ a b) ≈ (let₂ hΓ a' b')
  := ⟨rby.let₂_congr hΓ ha.left hb.left, rby.let₂_congr hΓ ha.right hb.right⟩

theorem Wf.equiv_inl_congr {Γ : Ctx? α} {A B} {a a' : Wf R Γ A} (ha : a ≈ a')
  : (inl A B a) ≈ (inl A B a')
  := ⟨rby.inl_congr ha.left, rby.inl_congr ha.right⟩

theorem Wf.equiv_inr_congr {Γ : Ctx? α} {A B} {b b' : Wf R Γ B} (hb : b ≈ b')
  : (inr A B b) ≈ (inr A B b')
  := ⟨rby.inr_congr hb.left, rby.inr_congr hb.right⟩

theorem Wf.equiv_case_congr {Γ Γl Γr : Ctx? α} {A B C} (hΓ : Γ.SSplit Γl Γr)
  {a a' : Wf R Γr (A.coprod B)} {b b' : Wf R (Γl.cons ⟨A, ⊤⟩) C} {c c' : Wf R (Γl.cons ⟨B, ⊤⟩) C}
  (ha : a ≈ a') (hb : b ≈ b') (hc : c ≈ c') : (case hΓ a b c) ≈ (case hΓ a' b' c')
  := ⟨rby.case_congr hΓ ha.left hb.left hc.left, rby.case_congr hΓ ha.right hb.right hc.right⟩

theorem Wf.equiv_abort_congr {Γ : Ctx? α} {A} {a a' : Wf R Γ Ty.empty} (ha : a ≈ a')
  : (abort A a) ≈ (abort A a')
  := ⟨rby.abort_congr ha.left, rby.abort_congr ha.right⟩

theorem Wf.equiv_iter_congr {Γ Γl Γr : Ctx? α} {A B : Ty α} (hΓ : Γ.SSplit Γl Γr)
  [hc : Γl.copy] [hd : Γl.del]
  {a a' : Wf R Γr A} {b b' : Wf R (Γl.cons ⟨A, ⊤⟩) (B.coprod A)}
  (ha : a ≈ a') (hb : b ≈ b') : (iter hΓ a b) ≈ (iter hΓ a' b')
  := ⟨rby.iter_congr hΓ ha.left hb.left, rby.iter_congr hΓ ha.right hb.right⟩

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

def Eqv.rby {Γ : Ctx? α} {A : Ty α} (a b : Eqv R Γ A) : Prop
  := liftOn₂ a b Wf.rby (λ_ _ _ _ ha hb
    => propext ⟨λ r => ha.right.trans (r.trans hb.left), λ r => ha.left.trans (r.trans hb.right)⟩)

theorem Wf.rby_quot_iff {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : Eqv.rby ⟦a⟧ ⟦b⟧ ↔ a.rby b
  := Iff.rfl

theorem Wf.rby_mk_iff {Γ : Ctx? α} {A : Ty α} (a b : Wf R Γ A) : e⟦a⟧.rby e⟦b⟧ ↔ a.rby b
  := Wf.rby_quot_iff a b

theorem Eqv.sound {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : a ≈ b) : e⟦a⟧ = e⟦b⟧
  := Quotient.sound h

theorem Eqv.exact {Γ : Ctx? α} {A : Ty α} {a b : Wf R Γ A} (h : e⟦a⟧ = e⟦b⟧) : a ≈ b
  := Quotient.exact h

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

def Eqv.op {Γ : Ctx? α} {f : φ} {A B} (hf : S.FnTy f A B) (a : Eqv R Γ A) : Eqv R Γ B
  := liftOn a (λa => e⟦a.op hf⟧) (λ_ _ h => Eqv.sound <| Wf.equiv_op_congr hf h)

def Eqv.let₁ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) B)
  : Eqv R Γ B := liftOn₂ a b (λa b => e⟦a.let₁ hΓ b⟧) (λ_ _ _ _ ha hb
    => Eqv.sound <| Wf.equiv_let₁_congr hΓ ha hb)

def Eqv.unit (Γ : Ctx? α) [hΓ : Γ.del] : Eqv R Γ Ty.unit
  := e⟦Wf.unit Γ⟧

def Eqv.pair {Γ Γl Γr : Ctx? α}  (hΓ : Γ.SSplit Γl Γr) {A B}
  (a : Eqv R Γl A) (b : Eqv R Γr B) : Eqv R Γ (Ty.tensor A B)
  := liftOn₂ a b (λa b => e⟦a.pair hΓ b⟧) (λ_ _ _ _ ha hb
    => Eqv.sound <| Wf.equiv_pair_congr hΓ ha hb)

def Eqv.let₂ {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (A.tensor B)) (b : Eqv R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C)
  : Eqv R Γ C := liftOn₂ a b (λa b => e⟦a.let₂ hΓ b⟧) (λ_ _ _ _ ha hb
    => Eqv.sound <| Wf.equiv_let₂_congr hΓ ha hb)

def Eqv.inl {Γ : Ctx? α} (A B) (a : Eqv R Γ A) : Eqv R Γ (Ty.coprod A B)
  := liftOn a (λa => e⟦a.inl A B⟧) (λ_ _ h => Eqv.sound <| Wf.equiv_inl_congr h)

def Eqv.inr {Γ : Ctx? α} (A B) (b : Eqv R Γ B) : Eqv R Γ (Ty.coprod A B)
  := liftOn b (λb => e⟦b.inr A B⟧) (λ_ _ h => Eqv.sound <| Wf.equiv_inr_congr h)

def Eqv.case {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr)
  (a : Eqv R Γr (A.coprod B)) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) C) (c : Eqv R (Γl.cons ⟨B, ⊤⟩) C)
  : Eqv R Γ C := liftOn₃ a b c (λa b c => e⟦a.case hΓ b c⟧)
    (λ_ _ _ _ _ _ ha hb hc => Eqv.sound <| Wf.equiv_case_congr hΓ ha hb hc)

def Eqv.abort {Γ : Ctx? α} (A) (a : Eqv R Γ Ty.empty) : Eqv R Γ A
  := liftOn a (λa => e⟦a.abort A⟧) (λ_ _ h => Eqv.sound <| Wf.equiv_abort_congr h)

def Eqv.iter {Γ Γl Γr : Ctx? α} (hΓ : Γ.SSplit Γl Γr) [hc : Γl.copy] [hd : Γl.del]
  (a : Eqv R Γr A) (b : Eqv R (Γl.cons ⟨A, ⊤⟩) (B.coprod A))
  : Eqv R Γ B := liftOn₂ a b (λa b => e⟦a.iter hΓ b⟧) (λ_ _ _ _ ha hb
    => Eqv.sound <| Wf.equiv_iter_congr hΓ ha hb)

--TODO: Wf HasEff

--TODO: Eqv term equivalence class

--TODO: Eqv HasEff (existential over equivalence class)
