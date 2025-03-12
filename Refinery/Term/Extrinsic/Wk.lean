import Refinery.Term.Extrinsic.Typing
import Refinery.Ctx.Basic

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

def Deriv.wkTerm {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a : Term φ (Ty α)}
  : (Δ ⊢ a : A) → Term φ (Ty α)
  | .bv (n := n) hv => .bv (ρ n)
  | .op (f := f) hf da => .op f (da.wkTerm ρ)
  | .let₁ (A := A) (B := B) hΓ da db =>
    .let₁ (da.wkTerm (hΓ.rightWk ρ)) A (db.wkTerm ((hΓ.leftWk ρ).scons _))
  | .unit _ => .unit
  | .pair hΓ da db =>
    .pair (da.wkTerm (hΓ.leftWk ρ)) (db.wkTerm (hΓ.rightWk ρ))
  | .let₂ (A := A) (B := B) hΓ da db =>
    .let₂ (da.wkTerm (hΓ.rightWk ρ)) A B (db.wkTerm (((hΓ.leftWk ρ).scons _).scons _))
  | .inl (A := A) (B := B) da => .inl A B (da.wkTerm ρ)
  | .inr (A := A) (B := B) db => .inr A B (db.wkTerm ρ)
  | .case (A := A) (B := B) hΓ da db dc =>
    .case (da.wkTerm (hΓ.rightWk ρ)) A B (db.wkTerm ((hΓ.leftWk ρ).scons _))
          (dc.wkTerm ((hΓ.leftWk ρ).scons _))
  | .abort (A := A) da => .abort A (da.wkTerm ρ)
  | .iter (A := A) (B := B) hΓ _ _ da db =>
    .iter (da.wkTerm (hΓ.rightWk ρ)) A B (db.wkTerm ((hΓ.leftWk ρ).scons _))

@[simp]
theorem Deriv.wkTerm_eq {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a : Term φ (Ty α)}
  (D : Δ ⊢ a : A) : D.wkTerm ρ = a.ren ρ
  := by induction D generalizing Γ <;> simp [wkTerm, *]

def Deriv.wkD {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a : Term φ (Ty α)}
  : (D : Δ ⊢ a : A) → (Γ ⊢ D.wkTerm ρ : A)
  | .bv hv => .bv (hv.wkIn ρ)
  | .op hf da => .op hf (da.wkD ρ)
  | .let₁ (A := A) (B := B) hΓ da db =>
    .let₁ (A := A) (B := B) (hΓ.wk ρ) (da.wkD (hΓ.rightWk ρ)) (db.wkD ((hΓ.leftWk ρ).scons _))
  | .unit hv => .unit (hv.wk ρ)
  | .pair hΓ da db =>
    .pair (hΓ.wk ρ) (da.wkD (hΓ.leftWk ρ)) (db.wkD (hΓ.rightWk ρ))
  | .let₂ (A := A) (B := B) hΓ da db =>
    .let₂ (A := A) (B := B) (hΓ.wk ρ) (da.wkD (hΓ.rightWk ρ))
      (db.wkD (((hΓ.leftWk ρ).scons _).scons _))
  | .inl (A := A) (B := B) da => .inl (da.wkD ρ)
  | .inr (A := A) (B := B) db => .inr (db.wkD ρ)
  | .case (A := A) (B := B) hΓ da db dc =>
    .case (hΓ.wk ρ) (da.wkD (hΓ.rightWk ρ)) (db.wkD ((hΓ.leftWk ρ).scons _))
          (dc.wkD ((hΓ.leftWk ρ).scons _))
  | .abort (A := A) da => .abort (da.wkD ρ)
  | .iter (A := A) (B := B) hΓ _ _ da db =>
    .iter (hΓ.wk ρ) (hΓ.wkLeft_copy ρ) (hΓ.wkLeft_del ρ)
                        (da.wkD (hΓ.rightWk ρ)) (db.wkD ((hΓ.leftWk ρ).scons _))

def Deriv.wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a : Term φ (Ty α)}
  (D : Δ ⊢ a : A) : (Γ ⊢ a.ren ρ : A)
  := (D.wkD ρ).cast_term (D.wkTerm_eq ρ)

def Deriv.wk0 {Γ : Ctx? α} (x : Var? α) [hx : x.del] {A : Ty α} {a : Term φ (Ty α)}
  (D : Γ ⊢ a : A) : (Γ.cons x ⊢ ↑⁰ a : A)
  := (D.wk ((Ctx?.Wk.refl Γ).skip hx)).cast_term (by simp [Nat.stepWk])

def Deriv.wk1 {Γ : Ctx? α} {v} (x : Var? α) [hx : x.del] {A : Ty α} {a : Term φ (Ty α)}
  (D : Γ.cons v ⊢ a : A) : ((Γ.cons x).cons v ⊢ ↑¹ a : A)
  := (D.wk (((Ctx?.Wk.refl Γ).skip hx).scons v)).cast_term (by simp [Nat.stepWk])

def Deriv.wk2 {Γ : Ctx? α} {l r} (x : Var? α) [hx : x.del] {A : Ty α} {a : Term φ (Ty α)}
  (D : (Γ.cons l).cons r ⊢ a : A) : (((Γ.cons x).cons l).cons r ⊢ ↑² a : A)
  := (D.wk ((((Ctx?.Wk.refl Γ).skip hx).scons l).scons r)).cast_term (by simp [Nat.stepWk])

@[simp]
theorem Deriv.wk_bv {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {n : ℕ} (x : Δ.At ⟨A, 1⟩ n)
  : (Deriv.bv x).wk ρ = (Deriv.bv (x.wkIn ρ)) := rfl

@[simp]
theorem Deriv.wk_op {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A B : Ty α} {a : Term φ (Ty α)}
  (hf : S.FnTy f A B) (da : Δ ⊢ a : A) : (da.op hf).wk ρ = (da.wk ρ).op hf
  := by simp [wk, wkD]

@[simp]
theorem Deriv.wk_let₁ {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A B : Ty α} {a b : Term φ (Ty α)}
  (hΓ : Δ.SSplit Δl Δr) (da : Δr ⊢ a : A) (db : Δl.cons ⟨A, ⊤⟩ ⊢ b : B)
  : (da.let₁ hΓ db).wk ρ
  = ((da.wk (hΓ.rightWk ρ)).cast_term (by simp)).let₁ (hΓ.wk ρ)
      ((db.wk ((hΓ.leftWk ρ).scons _)).cast_term (by simp))
  := by simp [wk, wkD]

@[simp]
theorem Deriv.wk_unit {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) (hv : Δ.del)
  : (Deriv.unit hv).wk ρ = Deriv.unit (hv.wk ρ) := rfl

@[simp]
theorem Deriv.wk_pair {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A B : Ty α} {a b : Term φ (Ty α)}
  (hΓ : Δ.SSplit Δl Δr) (da : Δl ⊢ a : A) (db : Δr ⊢ b : B)
  : (da.pair hΓ db).wk ρ
  = ((da.wk (hΓ.leftWk ρ)).cast_term (by simp)).pair (hΓ.wk ρ)
      ((db.wk (hΓ.rightWk ρ)).cast_term (by simp))
  := by simp [wk, wkD]

@[simp]
theorem Deriv.wk_let₂ {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A B C : Ty α} {a b : Term φ (Ty α)}
  (hΓ : Δ.SSplit Δl Δr) (da : Δr ⊢ a : A.tensor B) (db : (Δl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b : C)
  : (da.let₂ hΓ db).wk ρ
  = ((da.wk (hΓ.rightWk ρ)).cast_term (by simp)).let₂ (hΓ.wk ρ)
      ((db.wk (((hΓ.leftWk ρ).scons _).scons _)).cast_term (by simp))
  := by simp [wk, wkD]

@[simp]
theorem Deriv.wk_inl {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A B : Ty α} {a : Term φ (Ty α)}
  (da : Δ ⊢ a : A)
  : (da.inl (B := B)).wk ρ = (da.wk ρ).inl
  := by simp [wk, wkD]

@[simp]
theorem Deriv.wk_inr {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A B : Ty α} {b : Term φ (Ty α)}
  (db : Δ ⊢ b : B)
  : (db.inr (A := A)).wk ρ = (db.wk ρ).inr
  := by simp [wk, wkD]

@[simp]
theorem Deriv.wk_abort {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A : Ty α} {a : Term φ (Ty α)}
  (da : Δ ⊢ a : Ty.empty)
  : (da.abort (A := A)).wk ρ = (da.wk ρ).abort
  := by simp [wk, wkD]

@[simp]
theorem Deriv.wk_case {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A B C : Ty α} {a b c : Term φ (Ty α)}
  (hΓ : Δ.SSplit Δl Δr) (da : Δr ⊢ a : A.coprod B) (db : (Δl.cons ⟨A, ⊤⟩) ⊢ b : C)
  (dc : (Δl.cons ⟨B, ⊤⟩) ⊢ c : C)
  : (da.case hΓ db dc).wk ρ
  = ((da.wk (hΓ.rightWk ρ)).cast_term (by simp)).case (hΓ.wk ρ)
      ((db.wk ((hΓ.leftWk ρ).scons _)).cast_term (by simp))
      ((dc.wk ((hΓ.leftWk ρ).scons _)).cast_term (by simp))
  := by simp [wk, wkD]

@[simp]
theorem Deriv.wk_iter {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {A B : Ty α} {a b : Term φ (Ty α)}
  (hΓ : Δ.SSplit Δl Δr) (hc : Δl.copy) (hd : Δl.del)
  (da : Δr ⊢ a : A) (db : Δl.cons ⟨A, ⊤⟩ ⊢ b : B.coprod A)
  : (da.iter hΓ hc hd db).wk ρ
  = ((da.wk (hΓ.rightWk ρ)).cast_term (by simp)).iter (hΓ.wk ρ) (hΓ.wkLeft_copy ρ)
      (hΓ.wkLeft_del ρ) ((db.wk ((hΓ.leftWk ρ).scons _)).cast_term (by simp))
  := by simp [wk, wkD]

theorem Deriv.wk_eq {Γ Δ : Ctx? α} (ρ ρ' : Γ.Wk Δ) (h : ρ = ρ') {A : Ty α} {a : Term φ (Ty α)}
  (D : Δ ⊢ a : A) : (D.wk ρ).cast_term (by rw [h]) = D.wk ρ'
  := by cases h; rfl

theorem Deriv.wk_eq_cast_term
  {Γ Δ : Ctx? α} (ρ ρ' : Γ.Wk Δ) (h : ρ = ρ') {A : Ty α} {a : Term φ (Ty α)}
  (ha : a.ren ρ = a') (ha' : a.ren ρ' = a')
  (D : Δ ⊢ a : A) : (D.wk ρ).cast_term ha = (D.wk ρ').cast_term ha'
  := by cases h; rfl

def Deriv.pwk {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A : Ty α} {a : Term φ (Ty α)}
  (D : Δ ⊢ a : A) : (Γ ⊢ a : A)
  := (D.wk ρ.toWk).cast_term (by simp [Ctx?.Wk.ix_pwk])

@[simp]
theorem Deriv.pwk_bv {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A : Ty α} {n : ℕ} (x : Δ.At ⟨A, 1⟩ n)
  : (Deriv.bv x).pwk ρ = Deriv.bv (x.pwk ρ) := by simp [pwk, Ctx?.At.wkIn_toWk]

@[simp]
theorem Deriv.pwk_op {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A B : Ty α} {a : Term φ (Ty α)}
  (hf : S.FnTy f A B) (da : Δ ⊢ a : A) : (da.op hf).pwk ρ = (da.pwk ρ).op hf
  := by simp [pwk]

@[simp]
theorem Deriv.pwk_let₁ {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A B : Ty α} {a b : Term φ (Ty α)}
  (hΓ : Δ.SSplit Δl Δr) (da : Δr ⊢ a : A) (db : Δl.cons ⟨A, ⊤⟩ ⊢ b : B)
  : (da.let₁ hΓ db).pwk ρ
  = (da.pwk (hΓ.rightPWk ρ)).let₁ (hΓ.wk ρ.toWk) (db.pwk ((hΓ.leftPWk ρ).scons _))
  := by
  simp only [pwk, wk_let₁, cast_term_let₁, cast_term_cast_term]
  congr 1 <;> apply wk_eq_cast_term <;> simp [Ctx?.SSplit.leftPWk, Ctx?.SSplit.rightPWk]

@[simp]
theorem Deriv.pwk_let₂ {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A B C : Ty α} {a b : Term φ (Ty α)}
  (hΓ : Δ.SSplit Δl Δr) (da : Δr ⊢ a : A.tensor B) (db : (Δl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b : C)
  : (da.let₂ hΓ db).pwk ρ
  = (da.pwk (hΓ.rightPWk ρ)).let₂ (hΓ.wk ρ.toWk) (db.pwk (((hΓ.leftPWk ρ).scons _).scons _))
  := by
  simp only [pwk, wk_let₂, cast_term_let₂, cast_term_cast_term]
  congr 1 <;> apply wk_eq_cast_term <;> simp [Ctx?.SSplit.leftPWk, Ctx?.SSplit.rightPWk]

@[simp]
theorem Deriv.pwk_unit {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) (hv : Δ.del)
  : (Deriv.unit hv).pwk ρ = Deriv.unit (hv.wk ρ) := rfl

@[simp]
theorem Deriv.pwk_pair {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A B : Ty α} {a b : Term φ (Ty α)}
  (hΓ : Δ.SSplit Δl Δr) (da : Δl ⊢ a : A) (db : Δr ⊢ b : B)
  : (da.pair hΓ db).pwk ρ
  = (da.pwk (hΓ.leftPWk ρ)).pair (hΓ.wk ρ.toWk) (db.pwk (hΓ.rightPWk ρ))
  := by
  simp only [pwk, wk_pair, cast_term_pair, cast_term_cast_term]
  congr 1 <;> apply wk_eq_cast_term <;> simp [Ctx?.SSplit.leftPWk, Ctx?.SSplit.rightPWk]

@[simp]
theorem Deriv.pwk_inl {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A B : Ty α} {a : Term φ (Ty α)}
  (da : Δ ⊢ a : A)
  : (da.inl (B := B)).pwk ρ = (da.pwk ρ).inl
  := by simp [pwk]

@[simp]
theorem Deriv.pwk_inr {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A B : Ty α} {b : Term φ (Ty α)}
  (db : Δ ⊢ b : B)
  : (db.inr (A := A)).pwk ρ = (db.pwk ρ).inr
  := by simp [pwk]

@[simp]
theorem Deriv.pwk_abort {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A : Ty α} {a : Term φ (Ty α)}
  (da : Δ ⊢ a : Ty.empty)
  : (da.abort (A := A)).pwk ρ = (da.pwk ρ).abort
  := by simp [pwk]

@[simp]
theorem Deriv.pwk_case {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A B C : Ty α} {a b c : Term φ (Ty α)}
  (hΓ : Δ.SSplit Δl Δr) (da : Δr ⊢ a : A.coprod B) (db : (Δl.cons ⟨A, ⊤⟩) ⊢ b : C)
  (dc : (Δl.cons ⟨B, ⊤⟩) ⊢ c : C)
  : (da.case hΓ db dc).pwk ρ
  = (da.pwk (hΓ.rightPWk ρ)).case (hΓ.wk ρ.toWk) (db.pwk ((hΓ.leftPWk ρ).scons _))
      (dc.pwk ((hΓ.leftPWk ρ).scons _))
  := by
  simp only [pwk, wk_case, cast_term_case, cast_term_cast_term]
  congr 1 <;> apply wk_eq_cast_term <;> simp [Ctx?.SSplit.leftPWk, Ctx?.SSplit.rightPWk]

@[simp]
theorem Deriv.pwk_iter {Γ Δ : Ctx? α} (ρ : Γ.PWk Δ) {A B : Ty α} {a b : Term φ (Ty α)}
  (hΓ : Δ.SSplit Δl Δr) (hc : Δl.copy) (hd : Δl.del)
  (da : Δr ⊢ a : A) (db : Δl.cons ⟨A, ⊤⟩ ⊢ b : B.coprod A)
  : (da.iter hΓ hc hd db).pwk ρ
  = (da.pwk (hΓ.rightPWk ρ)).iter (hΓ.wk ρ.toWk) (hΓ.wkLeft_copy ρ.toWk) (hΓ.wkLeft_del ρ.toWk)
      (db.pwk ((hΓ.leftPWk ρ).scons _))
  := by
  simp only [pwk, wk_iter, cast_term_iter, cast_term_cast_term]
  congr 1 <;> apply wk_eq_cast_term <;> simp [Ctx?.SSplit.leftPWk, Ctx?.SSplit.rightPWk]

-- theorem Deriv.wk_heq_ofEq {Γ Δ : Ctx? α} (h : Γ = Δ) {A : Ty α} {a : Term φ (Ty α)}
--   (D : Δ ⊢ a : A) : HEq (D.wk (.ofEq h)) D
--   := by induction a generalizing Γ Δ A with
--   | let₁ _ _ _ Ia Ib =>
--     cases D
--     simp? [ren.eq_3, wk_let₁, Ctx?.Wk.ix.eq_2]
--     congr
--     simp
--     simp
--     sorry
--   | _ => sorry


-- theorem Deriv.wk_ofEq {Γ Δ : Ctx? α} (h : Γ = Δ) {A : Ty α} {a : Term φ (Ty α)}
--   (D : Δ ⊢ a : A) : D.wk (.ofEq h) = D.cast h.symm rfl (by cases h; simp)
--   := by induction a generalizing Γ Δ A with
--   | let₁ _ _ _ Ia Ib =>
--     cases D
--     simp only [ren, wk_let₁, Ctx?.Wk.ix.eq_2, cast_let₁, let₁.injEq, Ctx?.SSplit.wkLeft_ofEq,
--       Ctx?.SSplit.wkRight_ofEq, true_and]
--     sorry
--   | _ => sorry

-- def Deriv.pwk_ofEq {Γ Δ : Ctx? α} (h : Γ = Δ) {A : Ty α} {a : Term φ (Ty α)}
--   (D : Δ ⊢ a : A) : D.pwk (.ofEq h) = D.cast_ctx h.symm
--   := by induction D <;> simp [*]

-- def Deriv.pwk_refl {Γ Δ : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
--   (D : Γ ⊢ a : A) : D.pwk (Ctx?.PWk.refl Γ) = D
--   := by induction D <;> simp [*]

end Term

end Refinery
