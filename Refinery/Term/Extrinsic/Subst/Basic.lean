import Refinery.Term.Extrinsic.Typing
import Refinery.Term.Extrinsic.Wk

namespace Refinery

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

namespace Term

open HasQuant

inductive Deriv? : Ctx? α → Var? α → Term φ (Ty α) → Type _
  | valid {Γ : Ctx? α} {a : Term φ (Ty α)} (A : Ty α) (q : Quant) (D : Γ ⊢ a : A)
    (hΓ : quant (Var?.mk A q) ≤ quant Γ) : Deriv? Γ ⟨A, q⟩ a
  | zero {Γ : Ctx? α} (hΓ : Γ.del) (a A) : Deriv? Γ ⟨A, 0⟩ a

notation Γ "⊢?" a ":" v => Deriv? Γ v a

abbrev Deriv?.erase {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)} (_D : Γ ⊢? a : v)
  : (Γ.erase ⊢? a : v.erase) := .zero inferInstance _ _

def Deriv?.ssplitLeft {Γ : Ctx? α} {u v w : Var? α} {a : Term φ (Ty α)}
  : (h : u.SSplit v w) → (Γ ⊢? a : u) → (h.leftCtx Γ ⊢? a : v)
  | .left _, D => D | .sboth _, D => D
  | .right _, D => D.erase

def Deriv?.ssplitRight {Γ : Ctx? α} {u v w : Var? α} {a : Term φ (Ty α)}
  : (h : u.SSplit v w) → (Γ ⊢? a : u) → (h.rightCtx Γ ⊢? a : w)
  | .left _, D => D.erase | .sboth _, D => D
  | .right _, D => D

def Deriv?.unused {Γ : Ctx? α} {v : Var? α} (hΓ : Γ.del)  (a : Term φ (Ty α)) (hv : v.unused)
  : (Γ ⊢? a : v) := match v with | ⟨A, 0⟩ => .zero hΓ a A

theorem Deriv?.copy {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)}
  (D : Γ ⊢? a : v) (hv : v.used) (hc : v.copy) : Γ.copy := by cases D with
  | valid A q D hΓ =>
    constructor
    rw [<-EQuant.coe_le_coe]
    apply le_trans _ hΓ
    simp [Var?.copy_iff] at hc
    simp [quant]
    constructor
    exact hc.q
    exact hc.ty.copy_le_quant
  | zero => cases hv

theorem Deriv?.del_of_unused {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)}
  (D : Γ ⊢? a : v) (hv : v.unused) : Γ.del := by cases D with
  | valid hv' D hΓ => cases hv
  | zero hΓ _ _ => exact hΓ

theorem Deriv?.del {Γ : Ctx? α} {v : Var? α} {a : Term φ (Ty α)}
  (D : Γ ⊢? a : v) (hd : v.del) : Γ.del := by cases D with
  | valid A q D hΓ => exact ⟨le_trans hd.del_le_quant (le_trans (by simp [quant]) hΓ)⟩
  | zero hΓ _ _ => exact hΓ

def Deriv?.wk {Γ Δ : Ctx? α} (ρ : Γ.Wk Δ) {v : Var? α} {a : Term φ (Ty α)}
  (hΓΔ : quant Δ ≤ quant Γ) : (D : Δ ⊢? a : v) → (Γ ⊢? a.ren ρ : v)
  | .valid A q D hΔ => .valid A q (D.wk ρ) (le_trans hΔ (EQuant.coe_le_coe.mpr hΓΔ))
  | .zero hΓ a A => .zero (hΓ.wk ρ) (a.ren ρ) A

inductive SubstDS (φ) {α ε} [S : Signature φ α ε] : Ctx? α → Ctx? α → Type _
  | nil {Γ} (hΓ : Γ.del) : SubstDS φ Γ .nil
  | cons {Γ Γl Γr Δ} {v} {a : Term φ _} (hΓ : Γ.SSplit Γl Γr)
    (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v) : SubstDS φ Γ (Δ.cons v)

def SubstDS.toSubst {Γ Δ} : SubstDS φ Γ Δ → Subst φ (Ty α)
  | .nil _, i => .invalid
  | .cons (a := a) .., 0 => a
  | .cons _ σ _, i + 1 => σ.toSubst i

abbrev SubstDS.get {Γ Δ} (σ : SubstDS φ Γ Δ) (i : ℕ) : Term φ (Ty α) := σ.toSubst.get i

@[simp]
theorem SubstDS.get_nil {Γ} (σ : SubstDS φ Γ .nil) : σ.toSubst.get i = .invalid := by cases σ; rfl

@[simp]
theorem SubstDS.get_cons_zero {Γ Γl Γr Δ : Ctx? α} {v} {a : Term φ _} (hΓ : Γ.SSplit Γl Γr)
  (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v)
  : (σ.cons hΓ da).toSubst.get 0 = a := by rfl

@[simp]
theorem SubstDS.get_cons_succ {Γ Γl Γr Δ : Ctx? α} {v} {a : Term φ _} (hΓ : Γ.SSplit Γl Γr)
  (σ : SubstDS φ Γl Δ) (da : Γr ⊢? a : v) (i : ℕ)
  : (σ.cons hΓ da).toSubst.get (i + 1) = σ.toSubst.get i := by rfl

instance SubstDS.coeSubst : CoeOut (SubstDS φ Γ Δ) (Subst φ (Ty α)) where
  coe := SubstDS.toSubst

def SubstDS.tailCtx {Γ Δ} : SubstDS φ Γ Δ → Ctx? α
  | .nil _ => Γ
  | .cons (Γl := Γl) .. => Γl

def SubstDS.headCtx {Γ Δ} : SubstDS φ Γ Δ → Ctx? α
  | .nil _ => Γ.erase
  | .cons (Γr := Γr) .. => Γr

def SubstDS.headSplit {Γ Δ} : (σ : SubstDS φ Γ Δ) → Γ.SSplit (σ.tailCtx) (σ.headCtx)
  | .nil _ => Γ.erase_right
  | .cons hΓ .. => hΓ

def SubstDS.head {Γ Δ} : SubstDS φ Γ Δ → Var? α
  | .nil _ => ⟨.unit, 0⟩
  | .cons (v := v) .. => v

def SubstDS.headD {Γ Δ} : (σ : SubstDS φ Γ Δ) → σ.headCtx ⊢? σ.get 0 : σ.head
  | .nil hΓ => .zero (by simp [headCtx]) _ _
  | .cons _ _ da => da

def SubstDS.tail {Γ Δ} : (σ : SubstDS φ Γ Δ) → SubstDS φ σ.tailCtx Δ.tail
  | .nil hΓ => .nil hΓ
  | .cons _ σ _ => σ

def SubstDS.wkIn {Γ' Γ Δ} (ρ : Γ'.Wk Γ) : SubstDS φ Γ Δ → SubstDS φ Γ' Δ
  | .nil hΓ => .nil (hΓ.wk ρ)
  | .cons hΓ σ da =>
    .cons (hΓ.wk' ρ) (σ.wkIn (hΓ.leftWk' ρ)) (da.wk (hΓ.rightWk' ρ) (hΓ.wkRight_quant' ρ))

structure SubstSSplit
  (φ) {α ε} [S : Signature φ α ε] (inCtx outCtx outLeft outRight : Ctx? α)
  where
  (inLeft inRight : Ctx? α)
  (ssplitIn : inCtx.SSplit inLeft inRight)
  (substLeft : SubstDS φ inLeft outLeft)
  (substRight : SubstDS φ inRight outRight)

def SubstSSplit.erase_right (Γ : Ctx? α) [hΓ : Γ.del] : SubstSSplit φ Γ .nil .nil .nil
  := ⟨Γ, Γ.erase, Γ.erase_right, .nil hΓ, .nil inferInstance⟩

def SubstSSplit.erase_left (Γ : Ctx? α) [hΓ : Γ.del] : SubstSSplit φ Γ .nil .nil .nil
  := ⟨Γ.erase, Γ, Γ.erase_left, .nil inferInstance, .nil hΓ⟩

def SubstDS.ssplit {Γ Δl Δr : Ctx? α}
  : SubstDS φ Γ Δ → Δ.SSplit Δl Δr → SubstSSplit φ Γ Δ Δl Δr
  | .nil hΓ, .nil => SubstSSplit.erase_left _
  | .cons (Γr := Γr) (v := v) (a := a) hΓ σ da, .cons hΔ hlr =>
    let s := σ.ssplit hΔ
    match hlr with
    | .left _ =>
      if hv : v.used then
        let Ξ := hΓ.c12_3_23 s.ssplitIn.comm
        let s1_23 : Γ.SSplit s.inRight Ξ := hΓ.s12_3_1_23 s.ssplitIn.comm
        let s23 : Ξ.SSplit s.inLeft Γr := hΓ.s12_3_23 s.ssplitIn.comm
        ⟨Ξ, s.inRight,
          s1_23.comm,
          s.substLeft.cons s23 da,
          s.substRight.cons s.inRight.erase_right (.zero inferInstance a _)⟩
      else
        let Ξ := hΓ.c12_3_23 s.ssplitIn
        let s1_23 : Γ.SSplit s.inLeft Ξ := hΓ.s12_3_1_23 s.ssplitIn
        let s23 : Ξ.SSplit s.inRight Γr := hΓ.s12_3_23 s.ssplitIn
        ⟨s.inLeft, Ξ,
          s1_23,
          s.substLeft.cons s.inLeft.erase_right (.unused inferInstance a (Var?.unused_iff.mpr hv)),
          s.substRight.cons s23 (.unused (da.del_of_unused (Var?.unused_iff.mpr hv)) a rfl)⟩
    | .right _ =>
      let Ξ := hΓ.c12_3_23 s.ssplitIn
      let s1_23 : Γ.SSplit s.inLeft Ξ := hΓ.s12_3_1_23 s.ssplitIn
      let s23 : Ξ.SSplit s.inRight Γr := hΓ.s12_3_23 s.ssplitIn
      ⟨s.inLeft, Ξ,
        s1_23,
        s.substLeft.cons s.inLeft.erase_right (.zero inferInstance a _),
        s.substRight.cons s23 da⟩
    | .sboth h =>
      if hv : v.used then
        have sr := Γr.both (hΓ := da.copy hv h.copy);
        ⟨hΓ.c12_34_13 s.ssplitIn sr, hΓ.c12_34_24 s.ssplitIn sr,
          hΓ.s12_34_13_24 s.ssplitIn sr,
          s.substLeft.cons (hΓ.s12_34_13 s.ssplitIn sr) da,
          s.substRight.cons (hΓ.s12_34_24 s.ssplitIn sr) da⟩
      else
        let Ξ := hΓ.c12_3_23 s.ssplitIn
        let s1_23 : Γ.SSplit s.inLeft Ξ := hΓ.s12_3_1_23 s.ssplitIn
        let s23 : Ξ.SSplit s.inRight Γr := hΓ.s12_3_23 s.ssplitIn
        ⟨s.inLeft, Ξ,
          s1_23,
          s.substLeft.cons s.inLeft.erase_right (.unused inferInstance a (Var?.unused_iff.mpr hv)),
          s.substRight.cons s23 da⟩

abbrev SubstDS.inLeft {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ) (hΔ : Δ.SSplit Δl Δr) : Ctx? α
  := (σ.ssplit hΔ).inLeft

abbrev SubstDS.inRight {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ) (hΔ : Δ.SSplit Δl Δr) : Ctx? α
  := (σ.ssplit hΔ).inRight

abbrev SubstDS.ssplitIn {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ) (hΔ : Δ.SSplit Δl Δr)
  : Γ.SSplit (σ.inLeft hΔ) (σ.inRight hΔ) := (σ.ssplit hΔ).ssplitIn

abbrev SubstDS.substLeft {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ) (hΔ : Δ.SSplit Δl Δr)
  : SubstDS φ (σ.inLeft hΔ) Δl := (σ.ssplit hΔ).substLeft

abbrev SubstDS.substRight {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ) (hΔ : Δ.SSplit Δl Δr)
  : SubstDS φ (σ.inRight hΔ) Δr := (σ.ssplit hΔ).substRight

instance SubstDS.split_del_left {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ) (hΔ : Δ.SSplit Δl Δr)
  [hl : Δl.del] : (σ.inLeft hΔ).del := by induction σ generalizing Δl Δr with
  | nil => cases hΔ; simp [inLeft, inLeft, ssplit, SubstSSplit.erase_left]
  | cons hΓ _ da I =>
    cases hΔ with | cons hΔ hvw =>
    simp only [inLeft, ssplit, ge_iff_le]
    have I' := I hΔ (hl := hl.tail);
    split
    · split
      case isTrue hv => apply Ctx?.SSplit.c12_3_23_del (h3 := da.del hl.head)
      case isFalse => exact I'
    · exact I'
    · split
      case isTrue hv => apply Ctx?.SSplit.c12_34_13_del (h3 := da.del hl.head)
      case isFalse => exact I'

instance SubstDS.split_copy_left {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ) (hΔ : Δ.SSplit Δl Δr)
  [hl : Δl.copy] : (σ.inLeft hΔ).copy := by induction σ generalizing Δl Δr with
  | nil => cases hΔ; simp [inLeft, inLeft, ssplit, SubstSSplit.erase_left]
  | cons hΓ _ da I =>
    cases hΔ with | cons hΔ hvw =>
    simp only [inLeft, ssplit, ge_iff_le]
    have I' := I hΔ (hl := hl.tail);
    split
    · split
      case isTrue hv => apply Ctx?.SSplit.c12_3_23_copy (h3 := da.copy hv hl.head)
      case isFalse => exact I'
    · exact I'
    · split
      case isTrue hv => apply Ctx?.SSplit.c12_34_13_copy (h3 := da.copy hv hl.head)
      case isFalse => exact I'

theorem SubstDS.del {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) [hΔ : Δ.del] : Γ.del
  := by
  generalize hΔ = hΔ
  induction σ with
  | nil => assumption
  | cons hΓ _ da hl =>
    have hΓl := hl hΔ.tail
    have hΓr := da.del hΔ.head
    apply hΓ.in_del

def SubstDS.at {Γ Δ : Ctx? α} {q : Quant}
  : (σ : SubstDS φ Γ Δ) → (hv : Δ.At ⟨A, q⟩ n) → Γ ⊢ σ.get n : A
  | .cons hΓ σ (.valid _ _ da _), .here d hvw
    => (da.pwk (hΓ.pwk_left_del (hΔ := σ.del))).cast_ty hvw.ty
  | .cons hΓ σ da, .there x hv => (σ.at x).pwk (hΓ.pwk_right_del (hΞ := da.del hv))

def Deriv?.bv0 (Γ : Ctx? α)
  : (v : Var? α) → Γ.erase.cons v ⊢? .bv (φ := φ) 0 : v
  | ⟨A, 0⟩ => .zero inferInstance _ _
  | ⟨A, (q : Quant)⟩ => .valid _ _ .bv0 (by simp)

def SubstDS.lift {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v : Var? α)
  : SubstDS φ (Γ.cons v) (Δ.cons v)
  := .cons (a := .bv 0)
           (.cons Γ.erase_right (.right _))
           (σ.wkIn (Γ.wk0 v.erase))
           (Deriv?.bv0 Γ v)

def Deriv.substTerm {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A : Ty α} {a : Term φ (Ty α)}
  : (Δ ⊢ a : A) → Term φ (Ty α)
  | .bv (n := n) hv => σ.get n
  | .op (f := f) hf da => .op f (da.substTerm σ)
  | .let₁ (A := A) (B := B) hΔ da db =>
    let s := σ.ssplit hΔ;
    .let₁ (da.substTerm s.substRight) A (db.substTerm (s.substLeft.lift _))
  | .unit hv => .unit
  | .pair hΔ da db =>
    let s := σ.ssplit hΔ;
    .pair (da.substTerm s.substLeft) (db.substTerm s.substRight)
  | .let₂ (A := A) (B := B) hΔ da db =>
    let s := σ.ssplit hΔ;
    .let₂ (da.substTerm s.substRight) A B (db.substTerm ((s.substLeft.lift _).lift _))
  | .inl (A := A) (B := B) da => .inl A B (da.substTerm σ)
  | .inr (A := A) (B := B) db => .inr A B (db.substTerm σ)
  | .case (A := A) (B := B) hΔ da db dc =>
    let s := σ.ssplit hΔ;
    .case (da.substTerm s.substRight) A B (db.substTerm (s.substLeft.lift _))
          (dc.substTerm (s.substLeft.lift _))
  | .abort (A := A) da => .abort A (da.substTerm σ)
  | .iter (A := A) (B := B) hΔ _ _ da db =>
    let s := σ.ssplit hΔ;
    .iter (da.substTerm s.substRight) A B (db.substTerm (s.substLeft.lift _))

def Deriv.substD {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A : Ty α} {a : Term φ (Ty α)}
  : (D : Δ ⊢ a : A) → (Γ ⊢ D.substTerm σ : A)
  | .bv hv => σ.at hv
  | .op hf da => .op hf (da.substD σ)
  | .let₁ hΔ da db =>
    let s := σ.ssplit hΔ;
    .let₁ s.ssplitIn (da.substD s.substRight) (db.substD (s.substLeft.lift _))
  | .unit _ => .unit σ.del
  | .pair hΔ da db =>
    let s := σ.ssplit hΔ;
    .pair s.ssplitIn (da.substD s.substLeft) (db.substD s.substRight)
  | .let₂ hΔ da db =>
    let s := σ.ssplit hΔ;
    .let₂ s.ssplitIn (da.substD s.substRight) (db.substD ((s.substLeft.lift _).lift _))
  | .inl da => .inl (da.substD σ)
  | .inr db => .inr (db.substD σ)
  | .case hΔ da db dc =>
    let s := σ.ssplit hΔ;
    .case s.ssplitIn (da.substD s.substRight) (db.substD (s.substLeft.lift _))
          (dc.substD (s.substLeft.lift _))
  | .abort da => .abort (da.substD σ)
  | .iter hΔ _ _ da db =>
    let s := σ.ssplit hΔ;
    .iter s.ssplitIn (σ.split_copy_left hΔ) (σ.split_del_left hΔ)
                        (da.substD s.substRight) (db.substD (s.substLeft.lift _))

theorem SubstDS.ssubst_toSubst {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ) (hΔ : Δ.SSplit Δl Δr)
  : (σ.ssplit hΔ).substLeft.toSubst = σ.toSubst ∧ (σ.ssplit hΔ).substRight.toSubst = σ.toSubst := by
  induction σ generalizing Δl Δr with
  | nil => cases hΔ; simp [substLeft, substRight, ssplit, toSubst, SubstSSplit.erase_left]
  | cons hΓ _ da I =>
  rename Var? α => v
  cases hΔ with
  | cons hΔ hlr => cases hlr with
  | right => constructor <;> ext i <;> cases i <;> simp [ssplit, (I _).left, (I _).right]
  | left | sboth =>
    if hv : v.used then
      simp only [ssplit]
      rw [dite_cond_eq_true (by simp [hv])]
      constructor <;> ext i <;> cases i <;> simp [(I _).left, (I _).right]
    else
      simp only [ssplit]
      rw [dite_cond_eq_false (by simp [hv])]
      constructor <;> ext i <;> cases i <;> simp [(I _).left, (I _).right]

@[simp]
theorem SubstDS.ssubst_substLeft_toSubst {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ)
  (hΔ : Δ.SSplit Δl Δr) : (σ.ssplit hΔ).substLeft.toSubst = σ.toSubst := (σ.ssubst_toSubst hΔ).left

@[simp]
theorem SubstDS.ssubst_substRight_toSubst {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ)
  (hΔ : Δ.SSplit Δl Δr) : (σ.ssplit hΔ).substRight.toSubst = σ.toSubst := (σ.ssubst_toSubst hΔ).right

@[simp]
theorem SubstDS.substLeft_toSubst {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ) (hΔ : Δ.SSplit Δl Δr)
  : (σ.substLeft hΔ).toSubst = σ.toSubst := (σ.ssubst_toSubst hΔ).left

@[simp]
theorem SubstDS.substRight_toSubst {Γ Δl Δr : Ctx? α} (σ : SubstDS φ Γ Δ) (hΔ : Δ.SSplit Δl Δr)
  : (σ.substRight hΔ).toSubst = σ.toSubst := (σ.ssubst_toSubst hΔ).right

@[simp]
theorem SubstDS.wkIn_toSubst {Γ' Γ Δ : Ctx? α} (ρ : Γ'.Wk Γ) (σ : SubstDS φ Γ Δ)
  : (σ.wkIn ρ).toSubst = σ.toSubst.renOut ρ := by
  induction σ generalizing Γ' with
  | nil => rfl
  | cons hΓ σ da I =>
    ext i
    cases i <;> simp [wkIn, Subst.renOut, *]

@[simp]
theorem SubstDS.lift_toSubst {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v : Var? α)
  : (σ.lift v).toSubst = σ.toSubst.lift := by
  ext i; cases i <;> simp [SubstDS.lift, Ctx?.wk0, Nat.stepWk]

theorem Deriv.substTerm_eq {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A : Ty α} {a : Term φ (Ty α)}
  (D : Δ ⊢ a : A) : D.substTerm σ = a.subst σ := by induction D generalizing Γ with
  | bv | unit => rfl
  | _ => simp only [substTerm, subst]; congr <;> simp [*]

def Deriv.subst {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) {A : Ty α} {a : Term φ (Ty α)}
  (D : Δ ⊢ a : A) : Γ ⊢ a.subst σ : A
  := (D.substD σ).cast_term (D.substTerm_eq σ)

def SubstDS.refl : (Γ : Ctx? α) → SubstDS φ Γ Γ
  | .nil => .nil inferInstance
  | .cons Γ v => (refl Γ).lift v

theorem SubstDS.lift_refl {Γ : Ctx? α} (v : Var? α)
  : (SubstDS.refl Γ).lift v = SubstDS.refl (S := S) (Γ.cons v) := rfl

def SubstDS.subst0 {Γ Γl Γr : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (hΓ : Γ.SSplit Γl Γr) (da : Γr ⊢ a : A) (q : Quant) (hq : q ⊓ quant A ≤ quant Γr)
  : SubstDS φ Γ (Γl.cons ⟨A, q⟩)
  := .cons hΓ (.refl Γl) (.valid _ _ da hq)

@[simp]
theorem SubstDS.subst0_get_zero {Γ Γl Γr : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (hΓ : Γ.SSplit Γl Γr) (da : Γr ⊢ a : A) (q : Quant) (hq : q ⊓ quant A ≤ quant Γr)
  : (SubstDS.subst0 hΓ da q hq).get 0 = a := rfl

@[simp]
theorem SubstDS.subst0_get_succ {Γ Γl Γr : Ctx? α} {A : Ty α} {a : Term φ (Ty α)}
  (hΓ : Γ.SSplit Γl Γr) (da : Γr ⊢ a : A) (q : Quant) (hq : q ⊓ quant A ≤ quant Γr) (i : ℕ)
  : (SubstDS.subst0 hΓ da q hq).get (i + 1) = (SubstDS.refl Γl).get i := rfl

@[simp]
theorem SubstDS.lift_get_zero {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v : Var? α)
  : (σ.lift v).get 0 = .bv 0 := rfl

@[simp]
theorem SubstDS.lift_get_succ {Γ Δ : Ctx? α} (σ : SubstDS φ Γ Δ) (v : Var? α) (i : ℕ)
  : (σ.lift v).get (i + 1) = ↑⁰ (σ.get i) := by simp [lift, Ctx?.wk0]; rfl

theorem SubstDS.refl_get {Γ : Ctx? α} (i : ℕ)
  : (SubstDS.refl (S := S) Γ).get i = if i < Γ.length then .bv i else .invalid := by
  induction Γ generalizing i with
  | nil => simp
  | cons Γ v I => cases i with
  | zero => simp [refl]
  | succ i =>
    simp [refl, I]
    split <;> rfl

end Term
