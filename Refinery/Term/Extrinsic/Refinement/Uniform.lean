import Refinery.Term.Extrinsic.Wk
import Refinery.Term.Extrinsic.Effect

namespace Refinery

open HasCommRel

namespace Term

abbrev RWS (φ α) := Ctx? α → Ty α → Term φ (Ty α) → Term φ (Ty α) → Prop

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

class RWS.IsWt (R : RWS φ α) : Prop where
  left_wt {Γ A a b} (hab : R Γ A a b) : Term.IsWt Γ A a
  right_wt {Γ A a b} (hab : R Γ A a b) : Term.IsWt Γ A b

instance RWS.instIsWtBot : IsWt (φ := φ) ⊥ where
  left_wt := False.elim
  right_wt := False.elim

theorem RWS.IsWt.mk' (R : RWS φ α)
  (both_wt : ∀ {Γ A a b}, R Γ A a b → Term.IsWt Γ A a ∧ Term.IsWt Γ A b)
  : R.IsWt where
  left_wt hab := (both_wt hab).left
  right_wt hab := (both_wt hab).right

inductive RWS.ref (R : RWS φ α) : RWS φ α
  | base {Γ A a b} : R Γ A a b → (Γ ⊢ a : A) → (Γ ⊢ b : A) → ref R Γ A a b
  | refl {Γ a A} : (Γ ⊢ a : A) → ref R Γ A a a
  | trans {Γ a b c A} : ref R Γ A a b → ref R Γ A b c → ref R Γ A a c

--TODO: inst ref wt

--TODO: ref mono

--TODO: ref idem

inductive RWS.equiv (R : RWS φ α) : RWS φ α
  | base {Γ A a b} : R Γ A a b → (Γ ⊢ a : A) → (Γ ⊢ b : A) → equiv R Γ A a b
  | refl {Γ a A} : (Γ ⊢ a : A) → equiv R Γ A a a
  | trans {Γ a b c A} : equiv R Γ A a b → equiv R Γ A b c → equiv R Γ A a c
  | symm {Γ a b A} : equiv R Γ A a b → equiv R Γ A b a

--TODO: inst equiv wt

--TODO: equiv mono

--TODO: equiv idem

--TODO: equiv ref

inductive RWS.cong (R : RWS φ α) : RWS φ α
  | op {Γ A B f a a'} :
    S.FnTy f A B → cong R Γ A a a' → cong R Γ B (a.op f) (a'.op f)
  | let₁ {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    cong R Γr A a a' → cong R (Γl.cons ⟨A, ⊤⟩) B b b'
      → cong R Γ B (.let₁ a A b) (.let₁ a' A b')
  | let₂ {Γ Γl Γr A B C a b a' b'} :
    Γ.SSplit Γl Γr →
    cong R Γr (.tensor A B) a a' → cong R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C b b'
      → cong R Γ C (.let₂ a A B b) (.let₂ a' A B b')
  | pair {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    cong R Γl A a a' → cong R Γr B b b' → cong R Γ (.tensor A B) (.pair a b) (.pair a' b')
  | inl {Γ A B a a'} : cong R Γ A a a' → cong R Γ (.coprod A B) (.inl A B a) (.inl A B a')
  | inr {Γ A B b b'} : cong R Γ B b b' → cong R Γ (.coprod A B) (.inr A B b) (.inr A B b')
  | abort {Γ A a a'} : cong R Γ .empty a a' → cong R Γ A (.abort A a) (.abort A a')
  | case {Γ Γl Γr A B C a b c a' b' c'} :
    Γ.SSplit Γl Γr →
    cong R Γr (A.coprod B) a a' →
    cong R (Γl.cons ⟨A, ⊤⟩) C b b' →
    cong R (Γl.cons ⟨B, ⊤⟩) C c c' →
    cong R Γ C (.case a A B b c) (.case a' A B b' c')
  | iter {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    Γl.copy → Γl.del →
    cong R Γr A a a' →
    cong R (Γl.cons ⟨A, ⊤⟩) (.coprod B A) b b' →
    cong R Γ B (.iter a A B b) (.iter a' A B b')
  | base {Γ A a b} : R Γ A a b → (Γ ⊢ a : A) → (Γ ⊢ b : A) → cong R Γ A a b
  | refl {Γ a A} : (Γ ⊢ a : A) → cong R Γ A a a
  | trans {Γ a b c A} : cong R Γ A a b → cong R Γ A b c → cong R Γ A a c

-- A version of uniformity which preserves _bivalidity_
inductive RWS.isoUniform (R : RWS φ α) : RWS φ α
  | op {Γ A B f a a'} :
    S.FnTy f A B → isoUniform R Γ A a a' → isoUniform R Γ B (a.op f) (a'.op f)
  | let₁ {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    isoUniform R Γr A a a' → isoUniform R (Γl.cons ⟨A, ⊤⟩) B b b'
      → isoUniform R Γ B (.let₁ a A b) (.let₁ a' A b')
  | let₂ {Γ Γl Γr A B C a b a' b'} :
    Γ.SSplit Γl Γr →
    isoUniform R Γr (.tensor A B) a a' → isoUniform R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C b b'
      → isoUniform R Γ C (.let₂ a A B b) (.let₂ a' A B b')
  | pair {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    isoUniform R Γl A a a' → isoUniform R Γr B b b'
      → isoUniform R Γ (.tensor A B) (.pair a b) (.pair a' b')
  | inl {Γ A B a a'}
    : isoUniform R Γ A a a' → isoUniform R Γ (.coprod A B) (.inl A B a) (.inl A B a')
  | inr {Γ A B b b'}
    : isoUniform R Γ B b b' → isoUniform R Γ (.coprod A B) (.inr A B b) (.inr A B b')
  | case {Γ Γl Γr A B C a b c a' b' c'} :
    Γ.SSplit Γl Γr →
    isoUniform R Γr (A.coprod B) a a' →
    isoUniform R (Γl.cons ⟨A, ⊤⟩) C b b' →
    isoUniform R (Γl.cons ⟨B, ⊤⟩) C c c' →
    isoUniform R Γ C (.case a A B b c) (.case a' A B b' c')
  | abort {Γ A a a'} : isoUniform R Γ .empty a a' → isoUniform R Γ A (.abort A a) (.abort A a')
  | iter {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    Γl.copy → Γl.del →
    isoUniform R Γr A a a' →
    isoUniform R (Γl.cons ⟨A, ⊤⟩) (.coprod B A) b b' →
    isoUniform R Γ B (.iter a A B b) (.iter a' A B b')
  | pos_unif {Γ Γc Γl Γm Γr e e' A B X a b b'} :
    Γ.SSplit Γc Γr → Γc.SSplit Γl Γm → Γc.copy → Γc.del → e ∈ S.iterative → e' ⇌ e →
    (Γr ⊢ a : A) → a.HasEff e → ((Γm.cons ⟨A, ⊤⟩) ⊢ s : X) → s.HasEff e' →
    ((Γl.cons ⟨X, ⊤⟩) ⊢ b : B.coprod X) → b.HasEff e →
    ((Γc.cons ⟨A, ⊤⟩) ⊢ b' : B.coprod A) → b'.HasEff e →
    isoUniform R (Γc.cons ⟨A, ⊤⟩) (.coprod B X)
      (.let₁ s X (↑¹ b))
      (.case b' B A (.inl B X (.bv 0)) (.inr B X (↑¹ s))) →
    isoUniform R Γ B (.let₁ a A (.iter s X B (↑¹ b))) (.iter a A B b')
  | neg_unif {Γ Γc Γl Γm Γr e e' A B X a b b'} :
    Γ.SSplit Γc Γr → Γc.SSplit Γl Γm → Γc.copy → Γc.del → e ∈ S.iterative → e' ⇌ e →
    (Γr ⊢ a : A) → a.HasEff e → ((Γm.cons ⟨A, ⊤⟩) ⊢ s : X) → s.HasEff e' →
    ((Γl.cons ⟨X, ⊤⟩) ⊢ b : B.coprod X) → b.HasEff e →
    ((Γc.cons ⟨A, ⊤⟩) ⊢ b' : B.coprod A) → b'.HasEff e →
    isoUniform R (Γc.cons ⟨A, ⊤⟩) (.coprod B X)
      (.case b' B A (.inl B X (.bv 0)) (.inr B X (↑¹ s)))
      (.let₁ s X (↑¹ b)) →
    isoUniform R Γ B (.iter a A B b') (.let₁ a A (.iter s X B (↑¹ b)))
  | base {Γ A a b} : R Γ A a b → (Γ ⊢ a : A) → (Γ ⊢ b : A) → isoUniform R Γ A a b
  | refl {Γ a A} : (Γ ⊢ a : A) → isoUniform R Γ A a a
  | trans {Γ a b c A} : isoUniform R Γ A a b → isoUniform R Γ A b c → isoUniform R Γ A a c

inductive RWS.uniform (R : RWS φ α) : RWS φ α
  | op {Γ A B f a a'} :
    S.FnTy f A B → uniform R Γ A a a' → uniform R Γ B (a.op f) (a'.op f)
  | let₁ {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    uniform R Γr A a a' → uniform R (Γl.cons ⟨A, ⊤⟩) B b b'
      → uniform R Γ B (.let₁ a A b) (.let₁ a' A b')
  | let₂ {Γ Γl Γr A B C a b a' b'} :
    Γ.SSplit Γl Γr →
    uniform R Γr (.tensor A B) a a' → uniform R ((Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩) C b b'
      → uniform R Γ C (.let₂ a A B b) (.let₂ a' A B b')
  | pair {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    uniform R Γl A a a' → uniform R Γr B b b' → uniform R Γ (.tensor A B) (.pair a b) (.pair a' b')
  | inl {Γ A B a a'} : uniform R Γ A a a' → uniform R Γ (.coprod A B) (.inl A B a) (.inl A B a')
  | inr {Γ A B b b'} : uniform R Γ B b b' → uniform R Γ (.coprod A B) (.inr A B b) (.inr A B b')
  | case {Γ Γl Γr A B C a b c a' b' c'} :
    Γ.SSplit Γl Γr →
    uniform R Γr (A.coprod B) a a' →
    uniform R (Γl.cons ⟨A, ⊤⟩) C b b' →
    uniform R (Γl.cons ⟨B, ⊤⟩) C c c' →
    uniform R Γ C (.case a A B b c) (.case a' A B b' c')
  | abort {Γ A a a'} : uniform R Γ .empty a a' → uniform R Γ A (.abort A a) (.abort A a')
  | iter {Γ Γl Γr A B a b a' b'} :
    Γ.SSplit Γl Γr →
    Γl.copy → Γl.del →
    uniform R Γr A a a' →
    uniform R (Γl.cons ⟨A, ⊤⟩) (.coprod B A) b b' →
    uniform R Γ B (.iter a A B b) (.iter a' A B b')
  | pos_unif {Γ Γc Γl Γm Γr e e' A B X a b b'} :
    Γ.SSplit Γc Γr → Γc.SSplit Γl Γm → Γc.copy → Γc.del → e ∈ S.iterative → e' ⇀ e →
    (Γr ⊢ a : A) → a.HasEff e → ((Γm.cons ⟨A, ⊤⟩) ⊢ s : X) → s.HasEff e' →
    ((Γl.cons ⟨X, ⊤⟩) ⊢ b : B.coprod X) → b.HasEff e →
    ((Γc.cons ⟨A, ⊤⟩) ⊢ b' : B.coprod A) → b'.HasEff e →
    uniform R (Γc.cons ⟨A, ⊤⟩) (.coprod B X)
      (.let₁ s X (↑¹ b))
      (.case b' B A (.inl B X (.bv 0)) (.inr B X (↑¹ s))) →
    uniform R Γ B (.let₁ a A (.iter s X B (↑¹ b))) (.iter a A B b')
  | neg_unif {Γ Γc Γl Γm Γr e e' A B X a b b'} :
    Γ.SSplit Γc Γr → Γc.SSplit Γl Γm → Γc.copy → Γc.del → e ∈ S.iterative → e' ↽ e →
    (Γr ⊢ a : A) → a.HasEff e → ((Γm.cons ⟨A, ⊤⟩) ⊢ s : X) → s.HasEff e' →
    ((Γl.cons ⟨X, ⊤⟩) ⊢ b : B.coprod X) → b.HasEff e →
    ((Γc.cons ⟨A, ⊤⟩) ⊢ b' : B.coprod A) → b'.HasEff e →
    uniform R (Γc.cons ⟨A, ⊤⟩) (.coprod B X)
      (.case b' B A (.inl B X (.bv 0)) (.inr B X (↑¹ s)))
      (.let₁ s X (↑¹ b)) →
    uniform R Γ B (.iter a A B b') (.let₁ a A (.iter s X B (↑¹ b)))
  | base {Γ A a b} : R Γ A a b → (Γ ⊢ a : A) → (Γ ⊢ b : A) → uniform R Γ A a b
  | refl {Γ a A} : (Γ ⊢ a : A) → uniform R Γ A a a
  | trans {Γ a b c A} : uniform R Γ A a b → uniform R Γ A b c → uniform R Γ A a c

theorem RWS.uniform.wt {R : RWS φ α} {Γ A a a'} (h : uniform R Γ A a a')
  : Term.IsWt Γ A a ∧ Term.IsWt Γ A a' := by induction h with
  | base | refl => constructor <;> constructor <;> assumption
  | pos_unif hΓ hΓc hc hd he hcomm da hae ds hse db hbe db' hbe' hrw I =>
    rename_i s Γ Γc Γl Γm Γr e e' A B X a b b'
    constructor <;> constructor
    · apply Deriv.let₁ hΓ da
      have _ := hΓc.left_copy
      have _ := hΓc.left_del
      apply Deriv.iter (hΓc.cons (.right _)) inferInstance inferInstance ds (db.wk1 ⟨A, 0⟩)
    · apply Deriv.iter hΓ inferInstance inferInstance da db'
  | neg_unif hΓ hΓc hc hd he hcomm da hae ds hse db hbe db' hbe' hrw I =>
    rename_i s Γ Γc Γl Γm Γr e e' A B X a b b'
    constructor <;> constructor
    · apply Deriv.iter hΓ inferInstance inferInstance da db'
    · apply Deriv.let₁ hΓ da
      have _ := hΓc.left_copy
      have _ := hΓc.left_del
      apply Deriv.iter (hΓc.cons (.right _)) inferInstance inferInstance ds (db.wk1 ⟨A, 0⟩)
  | _ =>
    simp only [Term.IsWt] at *
    cases_type* And Nonempty
    constructor <;> constructor
    <;> first | assumption | (constructor <;> first | exact S.top_iterative | assumption)

--TODO: inst uniform wt

theorem RWS.uniform.mono {R : RWS φ α} {Γ A a a'} (h : uniform R Γ A a a') (hR : R ≤ R')
  : uniform R' Γ A a a' := by induction h with
  | base h da db => exact base (hR _ _ _ _ h) da db
  | refl => apply refl; assumption
  | trans => apply trans <;> assumption
  | _ => constructor <;> assumption

--TODO: uniform mono

--TODO: uniform idem

--TODO: uniform ref

inductive RWS.symm (R : RWS φ α) : RWS φ α
  | fwd {Γ A a b} : R Γ A a b → symm R Γ A a b
  | bwd {Γ A a b} : R Γ A b a → symm R Γ A a b

--TODO: uniform equiv == uniform symm

theorem RWS.symm_iff {R : RWS φ α} {Γ A a b} : symm R Γ A a b ↔ R Γ A a b ∨ R Γ A b a :=
  ⟨λ h => match h with
    | RWS.symm.fwd h => Or.inl h
    | RWS.symm.bwd h => Or.inr h,
  λ h => match h with
    | Or.inl h => RWS.symm.fwd h
    | Or.inr h => RWS.symm.bwd h⟩

inductive RWS.swap (R : RWS φ α) : RWS φ α
  | mk {Γ A a b} : R Γ A b a → swap R Γ A a b

theorem RWS.swap.get {R : RWS φ α} {Γ A a b} (h : swap R Γ A a b)
  : R Γ A b a := by cases h; assumption

theorem RWS.swap_iff {R : RWS φ α} {Γ A a b} : swap R Γ A a b ↔ R Γ A b a :=
  ⟨RWS.swap.get, RWS.swap.mk⟩

inductive RWS.iso (R : RWS φ α) : RWS φ α
  | mk {Γ A a b} : R Γ A a b → R Γ A b a → iso R Γ A a b

theorem RWS.iso.fwd {R : RWS φ α} {Γ A a b} (h : iso R Γ A a b)
  : R Γ A a b := by cases h; assumption

theorem RWS.iso.bwd {R : RWS φ α} {Γ A a b} (h : iso R Γ A a b)
  : R Γ A b a := by cases h; assumption

theorem RWS.iso_iff {R : RWS φ α} {Γ A a b} : iso R Γ A a b ↔ R Γ A a b ∧ R Γ A b a :=
  ⟨λ h => ⟨RWS.iso.fwd h, RWS.iso.bwd h⟩, λ ⟨h₁, h₂⟩ => RWS.iso.mk h₁ h₂⟩

-- instance RWS.uniform.instWt (R : RWS φ α) : RWS.IsWt (RWS.uniform R) where
--   left_wt h := (RWS.uniform.wt h).left
--   right_wt h := (RWS.uniform.wt h).right

-- inductive Rewrite : RWS φ α
--   | let_op {Γ Γl Γr A B C a c} :
--     Γ.SSplit Γl Γr → S.IsFn f e A B → (Γr ⊢ a : A) → (Γl.cons ⟨B, ⊤⟩ ⊢ c : C) →
--     Rewrite Γ C (.let₁ (.op f a) A c) (.let₁ a A (.let₁ (.op f (.bv 0)) B (↑¹ c)))
--   -- | let_let₁ {Γ Γc Γl Γm Γr} :
--   --   Γ.SSplit Γc Γr → Γc.SSplit Γl Γm → Rewrite R _ _ .invalid .invalid

abbrev DRWS (φ α) [S : Signature φ α ε]
  := (Γ : Ctx? α) → (A : Ty α) → (a b : Term φ (Ty α)) → (Γ ⊢ a : A) → (Γ ⊢ b : A) → Prop

abbrev DRWS.rel (R : DRWS φ α)
  {Γ : Ctx? α} {A : Ty α} {a b : Term φ (Ty α)} (da : Γ ⊢ a : A) (db : Γ ⊢ b : A) : Prop
  := R Γ A a b da db

class DRWS.Coherent (R : DRWS φ α) : Prop where
  elim {Γ A a b} (da da' : Γ ⊢ a : A) (db db' : Γ ⊢ b : A) : R.rel da db → R.rel da' db'

theorem DRWS.coh {R : DRWS φ α} [Coherent R] {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} (h : R.rel da db)
  (da' : Γ ⊢ a : A) (db' : Γ ⊢ b : A) : R.rel da' db'
  := Coherent.elim da da' db db' h

def DRWS.toRWS (R : DRWS φ α) : RWS φ α
  := λΓ A a b => ∃da : (Γ ⊢ a : A), ∃db : (Γ ⊢ b : A), R.rel da db

def RWS.toDRWS (R : RWS φ α) : DRWS φ α
  := λΓ A a b _ _ => R Γ A a b

theorem DRWS.toDRWS_toRWS_coherent (R : DRWS φ α) [hR : Coherent R] : R.toRWS.toDRWS = R := by
  ext Γ A a b da db
  simp only [RWS.toDRWS, toRWS]
  constructor
  intro ⟨da', db', h⟩; exact hR.elim da' da db' db h
  intro h; exact ⟨_, _, h⟩

instance RWS.toDRWS_coherent (R : RWS φ α) : DRWS.Coherent R.toDRWS where
  elim _ _ _ _ h := h

def DRWS.cohere (R : DRWS φ α) : DRWS φ α := R.toRWS.toDRWS

instance DRWS.cohere_coherent (R : DRWS φ α) : Coherent R.cohere := R.toRWS.toDRWS_coherent

theorem DRWS.cohere_increasing (R : DRWS φ α) : R ≤ R.cohere := λ_ _ _ _ _ _ h => ⟨_, _, h⟩

inductive DRWS.ref (R : DRWS φ α) : DRWS φ α
  | base {Γ A a b} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} : R.rel da db → ref R _ _ _ _ da db
  | refl {Γ a A} : (da da' : Γ ⊢ a : A) → ref R _ _ _ _ da da'
  | trans {Γ a b c A} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} {dc : Γ ⊢ c : A}
    : ref R _ _ _ _ da db → ref R _ _ _ _ db dc → ref R _ _ _ _ da dc

instance DRWS.ref_coherent (R : DRWS φ α) : Coherent R.ref where
  elim da da' db db' h := .trans (.refl da' da) (.trans h (.refl db db'))

--TODO: DRWS.ref friends

inductive DRWS.equiv (R : DRWS φ α) : DRWS φ α
  | base {Γ A a b} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} : R.rel da db → equiv R _ _ _ _ da db
  | refl {Γ a A} : (da da' : Γ ⊢ a : A) → equiv R _ _ _ _ da da'
  | trans {Γ a b c A} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} {dc : Γ ⊢ c : A}
    : equiv R _ _ _ _ da db → equiv R _ _ _ _ db dc → equiv R _ _ _ _ da dc
  | symm {Γ A a b} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} : equiv R _ _ _ _ da db → equiv R _ _ _ _ db da

instance DRWS.equiv_coherent (R : DRWS φ α) : Coherent R.equiv where
  elim da da' db db' h := .trans (.refl da' da) (.trans h (.refl db db'))

--TODO: DRWS.equiv friends

inductive DRWS.cong (R : DRWS φ α) : DRWS φ α
  | op {Γ A B f a a'}
    {da : Γ ⊢ a : A} {da' : Γ ⊢ a' : A}
    (hf : S.FnTy f A B) : cong R _ _ _ _ da da' → cong R _ _ _ _ (da.op hf) (da'.op hf)
  | let₁ {Γ Γl Γr : Ctx? α} {A B a b a' b'}
    {da : Γr ⊢ a : A} {da' : Γr ⊢ a' : A}
    {db : Γl.cons ⟨A, ⊤⟩ ⊢ b : B} {db' : Γl.cons ⟨A, ⊤⟩ ⊢ b' : B}
    (hΓ : Γ.SSplit Γl Γr) : cong R _ _ _ _ da da' → cong R _ _ _ _ db db'
      → cong R _ _ _ _ (da.let₁ hΓ db) (da'.let₁ hΓ db')
  | let₂ {Γ Γl Γr : Ctx? α} {A B C a b a' b'}
    {da : Γr ⊢ a : A.tensor B} {da' : Γr ⊢ a' : A.tensor B}
    {db : (Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b : C} {db' : (Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b' : C}
    (hΓ : Γ.SSplit Γl Γr) : cong R _ _ _ _ da da' → cong R _ _ _ _ db db'
      → cong R _ _ _ _ (da.let₂ hΓ db) (da'.let₂ hΓ db')
  | pair {Γ Γl Γr : Ctx? α} {A B a b a' b'}
    {da : Γl ⊢ a : A} {da' : Γl ⊢ a' : A} {db : Γr ⊢ b : B} {db' : Γr ⊢ b' : B}
    (hΓ : Γ.SSplit Γl Γr) : cong R _ _ _ _ da da' → cong R _ _ _ _ db db'
      → cong R _ _ _ _ (da.pair hΓ db) (da.pair hΓ db)
  | inl {Γ A B a a'}
    {da : Γ ⊢ a : A} {da' : Γ ⊢ a' : A}
    : cong R _ _ _ _ da da' → cong R _ _ _ _ (da.inl (B := B)) (da'.inl (B := B))
  | inr {Γ A B b b'}
    {db : Γ ⊢ b : B} {db' : Γ ⊢ b' : B}
    : cong R _ _ _ _ db db' → cong R _ _ _ _ (db.inr (A := A)) (db'.inr (A := A))
  | abort {Γ A a a'}
    {da : Γ ⊢ a : Ty.empty} {da' : Γ ⊢ a' : Ty.empty}
    : cong R _ _ _ _ da da' → cong R _ _ _ _ (da.abort (A := A)) (da'.abort (A := A))
  | case {Γ Γl Γr : Ctx? α} {A B a b c a' b' c' C}
    {da : Γr ⊢ a : A.coprod B} {db : Γl.cons ⟨A, ⊤⟩ ⊢ b : C} {dc : Γl.cons ⟨B, ⊤⟩ ⊢ c : C}
    {da' : Γr ⊢ a' : A.coprod B} {db' : Γl.cons ⟨A, ⊤⟩ ⊢ b' : C} {dc' : Γl.cons ⟨B, ⊤⟩ ⊢ c' : C}
    (hΓ : Γ.SSplit Γl Γr)
    : cong R _ _ _ _ da da' → cong R _ _ _ _ db db' → cong R _ _ _ _ dc dc'
    → cong R _ _ _ _ (da.case hΓ db dc) (da'.case hΓ db' dc')
  | iter {Γ Γl Γr : Ctx? α} {A B : Ty α} {a b a' b'}
    {da : Γr ⊢ a : A} {da' : Γr ⊢ a' : A}
    {db : Γl.cons ⟨A, ⊤⟩ ⊢ b : B.coprod A} {db' : Γl.cons ⟨A, ⊤⟩ ⊢ b' : B.coprod A}
    (hΓ : Γ.SSplit Γl Γr) (hc : Γl.copy) (hd : Γl.del)
    : cong R _ _ _ _ da da' → cong R _ _ _ _ db db'
    → cong R _ _ _ _ (da.iter hΓ hc hd db) (da'.iter hΓ hc hd db')
  | base {Γ A a b} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} : R.rel da db → cong R _ _ _ _ da db
  | refl {Γ a A} : (da da' : Γ ⊢ a : A) → cong R _ _ _ _ da da'
  | trans {Γ a b c A} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} {dc : Γ ⊢ c : A}
    : cong R _ _ _ _ da db → cong R _ _ _ _ db dc → cong R _ _ _ _ da dc

--TODO: DRWS.cong + friends

inductive DRWS.isoUniform (R : DRWS φ α) : DRWS φ α
  | op {Γ A B f a a'}
    {da : Γ ⊢ a : A} {da' : Γ ⊢ a' : A}
    (hf : S.FnTy f A B) : isoUniform R _ _ _ _ da da' → isoUniform R _ _ _ _ (da.op hf) (da'.op hf)
  | let₁ {Γ Γl Γr : Ctx? α} {A B a b a' b'}
    {da : Γr ⊢ a : A} {da' : Γr ⊢ a' : A}
    {db : Γl.cons ⟨A, ⊤⟩ ⊢ b : B} {db' : Γl.cons ⟨A, ⊤⟩ ⊢ b' : B}
    (hΓ : Γ.SSplit Γl Γr) : isoUniform R _ _ _ _ da da' → isoUniform R _ _ _ _ db db'
      → isoUniform R _ _ _ _ (da.let₁ hΓ db) (da'.let₁ hΓ db')
  | let₂ {Γ Γl Γr : Ctx? α} {A B C a b a' b'}
    {da : Γr ⊢ a : A.tensor B} {da' : Γr ⊢ a' : A.tensor B}
    {db : (Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b : C} {db' : (Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b' : C}
    (hΓ : Γ.SSplit Γl Γr) : isoUniform R _ _ _ _ da da' → isoUniform R _ _ _ _ db db'
      → isoUniform R _ _ _ _ (da.let₂ hΓ db) (da'.let₂ hΓ db')
  | pair {Γ Γl Γr : Ctx? α} {A B a b a' b'}
    {da : Γl ⊢ a : A} {da' : Γl ⊢ a' : A} {db : Γr ⊢ b : B} {db' : Γr ⊢ b' : B}
    (hΓ : Γ.SSplit Γl Γr) : isoUniform R _ _ _ _ da da' → isoUniform R _ _ _ _ db db'
      → isoUniform R _ _ _ _ (da.pair hΓ db) (da.pair hΓ db)
  | inl {Γ A B a a'}
    {da : Γ ⊢ a : A} {da' : Γ ⊢ a' : A}
    : isoUniform R _ _ _ _ da da' → isoUniform R _ _ _ _ (da.inl (B := B)) (da'.inl (B := B))
  | inr {Γ A B b b'}
    {db : Γ ⊢ b : B} {db' : Γ ⊢ b' : B}
    : isoUniform R _ _ _ _ db db' → isoUniform R _ _ _ _ (db.inr (A := A)) (db'.inr (A := A))
  | abort {Γ A a a'}
    {da : Γ ⊢ a : Ty.empty} {da' : Γ ⊢ a' : Ty.empty}
    : isoUniform R _ _ _ _ da da' → isoUniform R _ _ _ _ (da.abort (A := A)) (da'.abort (A := A))
  | case {Γ Γl Γr : Ctx? α} {A B a b c a' b' c' C}
    {da : Γr ⊢ a : A.coprod B} {db : Γl.cons ⟨A, ⊤⟩ ⊢ b : C} {dc : Γl.cons ⟨B, ⊤⟩ ⊢ c : C}
    {da' : Γr ⊢ a' : A.coprod B} {db' : Γl.cons ⟨A, ⊤⟩ ⊢ b' : C} {dc' : Γl.cons ⟨B, ⊤⟩ ⊢ c' : C}
    (hΓ : Γ.SSplit Γl Γr)
    : isoUniform R _ _ _ _ da da' → isoUniform R _ _ _ _ db db' → isoUniform R _ _ _ _ dc dc'
    → isoUniform R _ _ _ _ (da.case hΓ db dc) (da'.case hΓ db' dc')
  | iter {Γ Γl Γr : Ctx? α} {A B : Ty α} {a b a' b'}
    {da : Γr ⊢ a : A} {da' : Γr ⊢ a' : A}
    {db : Γl.cons ⟨A, ⊤⟩ ⊢ b : B.coprod A} {db' : Γl.cons ⟨A, ⊤⟩ ⊢ b' : B.coprod A}
    (hΓ : Γ.SSplit Γl Γr) (hc : Γl.copy) (hd : Γl.del)
    : isoUniform R _ _ _ _ da da' → isoUniform R _ _ _ _ db db'
    → isoUniform R _ _ _ _ (da.iter hΓ hc hd db) (da'.iter hΓ hc hd db')
  | pos_unif {Γ Γc Γl Γm Γr : Ctx? α} {e e'} {A B X : Ty α} {a b b'}
    {da : Γr ⊢ a : A} {ds : Γm.cons ⟨A, ⊤⟩ ⊢ s : X}
    {db : Γl.cons ⟨X, ⊤⟩ ⊢ b : B.coprod X} {db' : Γc.cons ⟨A, ⊤⟩ ⊢ b' : B.coprod A}
    (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
    (hc : Γc.copy) (hd : Γc.del) (hcl : Γl.copy) (hdl : Γl.del)
    : a.HasEff e → s.HasEff e' → b.HasEff e → b'.HasEff e → e ∈ S.iterative → e' ⇌ e
      → isoUniform R _ _ _ _
          (ds.let₁ (hΓc.cons (.right _)) (db.wk1 _))
          (db'.case (Γc.both.cons (.right _))
            (Deriv.bv (.here inferInstance Var?.Wk.top_le_quant)).inl
            ((ds.pwk ((hΓc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
      → isoUniform R _ _ _ _
        (da.let₁ hΓ (ds.iter (hΓc.cons (.right _)) inferInstance inferInstance (db.wk1 _)))
        (da.iter hΓ hc hd db')
  | neg_unif {Γ Γc Γl Γm Γr : Ctx? α} {e e'} {A B X : Ty α} {a b b'}
    {da : Γr ⊢ a : A} {ds : Γm.cons ⟨A, ⊤⟩ ⊢ s : X}
    {db : Γl.cons ⟨X, ⊤⟩ ⊢ b : B.coprod X} {db' : Γc.cons ⟨A, ⊤⟩ ⊢ b' : B.coprod A}
    (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
    (hc : Γc.copy) (hd : Γc.del) (hcl : Γl.copy) (hdl : Γl.del)
    : a.HasEff e → s.HasEff e' → b.HasEff e → b'.HasEff e → e ∈ S.iterative → e' ⇌ e
      → isoUniform R _ _ _ _
          (db'.case (Γc.both.cons (.right _))
            (Deriv.bv (.here inferInstance Var?.Wk.top_le_quant)).inl
            ((ds.pwk ((hΓc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
          (ds.let₁ (hΓc.cons (.right _)) (db.wk1 _))
      → isoUniform R _ _ _ _
        (da.iter hΓ hc hd db')
        (da.let₁ hΓ (ds.iter (hΓc.cons (.right _)) inferInstance inferInstance (db.wk1 _)))
  | base {Γ A a b} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} : R.rel da db → isoUniform R _ _ _ _ da db
  | refl {Γ a A} : (da da' : Γ ⊢ a : A) → isoUniform R _ _ _ _ da da'
  | trans {Γ a b c A} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} {dc : Γ ⊢ c : A}
    : isoUniform R _ _ _ _ da db → isoUniform R _ _ _ _ db dc → isoUniform R _ _ _ _ da dc

--TODO: DRWS.isoUniform + friends

inductive DRWS.uniform (R : DRWS φ α) : DRWS φ α
  | op {Γ A B f a a'}
    {da : Γ ⊢ a : A} {da' : Γ ⊢ a' : A}
    (hf : S.FnTy f A B) : uniform R _ _ _ _ da da' → uniform R _ _ _ _ (da.op hf) (da'.op hf)
  | let₁ {Γ Γl Γr : Ctx? α} {A B a b a' b'}
    {da : Γr ⊢ a : A} {da' : Γr ⊢ a' : A}
    {db : Γl.cons ⟨A, ⊤⟩ ⊢ b : B} {db' : Γl.cons ⟨A, ⊤⟩ ⊢ b' : B}
    (hΓ : Γ.SSplit Γl Γr) : uniform R _ _ _ _ da da' → uniform R _ _ _ _ db db'
      → uniform R _ _ _ _ (da.let₁ hΓ db) (da'.let₁ hΓ db')
  | let₂ {Γ Γl Γr : Ctx? α} {A B C a b a' b'}
    {da : Γr ⊢ a : A.tensor B} {da' : Γr ⊢ a' : A.tensor B}
    {db : (Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b : C} {db' : (Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b' : C}
    (hΓ : Γ.SSplit Γl Γr) : uniform R _ _ _ _ da da' → uniform R _ _ _ _ db db'
      → uniform R _ _ _ _ (da.let₂ hΓ db) (da'.let₂ hΓ db')
  | pair {Γ Γl Γr : Ctx? α} {A B a b a' b'}
    {da : Γl ⊢ a : A} {da' : Γl ⊢ a' : A} {db : Γr ⊢ b : B} {db' : Γr ⊢ b' : B}
    (hΓ : Γ.SSplit Γl Γr) : uniform R _ _ _ _ da da' → uniform R _ _ _ _ db db'
      → uniform R _ _ _ _ (da.pair hΓ db) (da'.pair hΓ db')
  | inl {Γ A B a a'}
    {da : Γ ⊢ a : A} {da' : Γ ⊢ a' : A}
    : uniform R _ _ _ _ da da' → uniform R _ _ _ _ (da.inl (B := B)) (da'.inl (B := B))
  | inr {Γ A B b b'}
    {db : Γ ⊢ b : B} {db' : Γ ⊢ b' : B}
    : uniform R _ _ _ _ db db' → uniform R _ _ _ _ (db.inr (A := A)) (db'.inr (A := A))
  | abort {Γ A a a'}
    {da : Γ ⊢ a : Ty.empty} {da' : Γ ⊢ a' : Ty.empty}
    : uniform R _ _ _ _ da da' → uniform R _ _ _ _ (da.abort (A := A)) (da'.abort (A := A))
  | case {Γ Γl Γr : Ctx? α} {A B a b c a' b' c' C}
    {da : Γr ⊢ a : A.coprod B} {db : Γl.cons ⟨A, ⊤⟩ ⊢ b : C} {dc : Γl.cons ⟨B, ⊤⟩ ⊢ c : C}
    {da' : Γr ⊢ a' : A.coprod B} {db' : Γl.cons ⟨A, ⊤⟩ ⊢ b' : C} {dc' : Γl.cons ⟨B, ⊤⟩ ⊢ c' : C}
    (hΓ : Γ.SSplit Γl Γr)
    : uniform R _ _ _ _ da da' → uniform R _ _ _ _ db db' → uniform R _ _ _ _ dc dc'
    → uniform R _ _ _ _ (da.case hΓ db dc) (da'.case hΓ db' dc')
  | iter {Γ Γl Γr : Ctx? α} {A B : Ty α} {a b a' b'}
    {da : Γr ⊢ a : A} {da' : Γr ⊢ a' : A}
    {db : Γl.cons ⟨A, ⊤⟩ ⊢ b : B.coprod A} {db' : Γl.cons ⟨A, ⊤⟩ ⊢ b' : B.coprod A}
    (hΓ : Γ.SSplit Γl Γr) (hc : Γl.copy) (hd : Γl.del)
    : uniform R _ _ _ _ da da' → uniform R _ _ _ _ db db'
    → uniform R _ _ _ _ (da.iter hΓ hc hd db) (da'.iter hΓ hc hd db')
  | pos_unif {Γ Γc Γl Γm Γr : Ctx? α} {e e'} {A B X : Ty α} {a b b'}
    {da : Γr ⊢ a : A} {ds : Γm.cons ⟨A, ⊤⟩ ⊢ s : X}
    {db : Γl.cons ⟨X, ⊤⟩ ⊢ b : B.coprod X} {db' : Γc.cons ⟨A, ⊤⟩ ⊢ b' : B.coprod A}
    (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
    (hc : Γc.copy) (hd : Γc.del)
    : a.HasEff e → s.HasEff e' → b.HasEff e → b'.HasEff e → e ∈ S.iterative → e' ⇀ e
      → uniform R _ _ _ _
          (ds.let₁ (hΓc.cons (.right _)) (db.wk1 _))
          (db'.case (Γc.both.cons (.right _))
            (Deriv.bv (.here inferInstance Var?.Wk.top_le_quant)).inl
            ((ds.pwk ((have _ := hΓc.left_del; hΓc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
      → uniform R _ _ _ _
        (da.let₁ hΓ (ds.iter (hΓc.cons (.right _))
          (have _ := hΓc.left_copy; inferInstance)
          (have _ := hΓc.left_del; inferInstance) (db.wk1 _)))
        (da.iter hΓ hc hd db')
  | neg_unif {Γ Γc Γl Γm Γr : Ctx? α} {e e'} {A B X : Ty α} {a b b'}
    {da : Γr ⊢ a : A} {ds : Γm.cons ⟨A, ⊤⟩ ⊢ s : X}
    {db : Γl.cons ⟨X, ⊤⟩ ⊢ b : B.coprod X} {db' : Γc.cons ⟨A, ⊤⟩ ⊢ b' : B.coprod A}
    (hΓ : Γ.SSplit Γc Γr) (hΓc : Γc.SSplit Γl Γm)
    (hc : Γc.copy) (hd : Γc.del)
    : a.HasEff e → s.HasEff e' → b.HasEff e → b'.HasEff e → e ∈ S.iterative → e' ↽ e
      → uniform R _ _ _ _
          (db'.case (Γc.both.cons (.right _))
            (Deriv.bv (.here inferInstance Var?.Wk.top_le_quant)).inl
            ((ds.pwk ((have _ := hΓc.left_del; hΓc.pwk_left_del).scons _)).wk1 ⟨A, 0⟩).inr)
          (ds.let₁ (hΓc.cons (.right _)) (db.wk1 _))
      → uniform R _ _ _ _
        (da.iter hΓ hc hd db')
        (da.let₁ hΓ (ds.iter (hΓc.cons (.right _))
          (have _ := hΓc.left_copy; inferInstance)
          (have _ := hΓc.left_del; inferInstance) (db.wk1 _)))
  | base {Γ A a b} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} : R.rel da db → uniform R _ _ _ _ da db
  | refl {Γ a A} : (da da' : Γ ⊢ a : A) → uniform R _ _ _ _ da da'
  | trans {Γ a b c A} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} {dc : Γ ⊢ c : A}
    : uniform R _ _ _ _ da db → uniform R _ _ _ _ db dc → uniform R _ _ _ _ da dc

instance DRWS.uniform_coherent (R : DRWS φ α) : Coherent R.uniform where
  elim da da' db db' h := .trans (.refl da' da) (.trans h (.refl db db'))

theorem DRWS.uniform.mono {R R' : DRWS φ α} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A}
  (h : R.uniform.rel da db) (hR : R ≤ R') : R'.uniform.rel da db := by induction h with
  | base r => exact uniform.base (hR _ _ _ _ _ _ r)
  | refl => apply uniform.refl
  | trans => apply uniform.trans <;> assumption
  | _ => constructor <;> assumption

theorem DRWS.uniform_mono {R R' : DRWS φ α} (hR : R ≤ R') : R.uniform ≤ R'.uniform
  := λ _ _ _ _ _ _ h => h.mono hR

theorem DRWS.uniform_increasing (R : DRWS φ α) : R ≤ R.uniform := λ _ _ _ _ _ _ h => uniform.base h

theorem DRWS.uniform_le_cohere (R : DRWS φ α) : R.cohere ≤ R.uniform
  := λ _ _ _ _ da' db' ⟨da, db, h⟩ => Coherent.elim da da' db db' (uniform.base h)

theorem DRWS.uniform.flatten {R : DRWS φ α} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A}
  (h : R.uniform.uniform.rel da db) : R.uniform.rel da db
  := by induction h with
  | base h => exact h
  | refl => apply uniform.refl
  | trans => apply uniform.trans <;> assumption
  | _ => constructor <;> assumption

theorem DRWS.uniform_idem (R : DRWS φ α) : R.uniform.uniform = R.uniform
  := le_antisymm (λ _ _ _ _ _ _ r => r.flatten) R.uniform.uniform_increasing

theorem DRWS.uniform_cohere (R : DRWS φ α) : R.cohere.uniform = R.uniform
  := le_antisymm
    (R.uniform_idem ▸ (uniform_mono R.uniform_le_cohere))
    (uniform_mono R.cohere_increasing)

theorem DRWS.uniform_toDRWS_toDWS (R : DRWS φ α) : R.toRWS.toDRWS.uniform = R.uniform
  := R.uniform_cohere

theorem DRWS.uniform.toRWS {R : DRWS φ α} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A}
  (h : R.uniform.rel da db) : R.toRWS.uniform Γ A a b
  := by induction h with
  | base h => apply RWS.uniform.base; exact ⟨_, _, h⟩; assumption; assumption
  | refl => apply RWS.uniform.refl; assumption
  | trans => apply RWS.uniform.trans <;> assumption
  | _ => constructor <;> assumption

theorem RWS.uniform.toDRWS {R : RWS φ α} {Γ A a b}
  (h : R.uniform Γ A a b) (da : Γ ⊢ a : A) (db : Γ ⊢ b : A)
  : R.toDRWS.uniform.rel da db := by
  induction h with
  | op hf ra Ia =>
    have ⟨Da⟩ := ra.wt.left;
    have ⟨Da'⟩ := ra.wt.right;
    exact DRWS.coh ((Ia Da Da').op hf) _ _
  | let₁ hΓ ra rb Ia Ib =>
    have ⟨Da⟩ := ra.wt.left;
    have ⟨Da'⟩ := ra.wt.right;
    have ⟨Db⟩ := rb.wt.left;
    have ⟨Db'⟩ := rb.wt.right;
    exact DRWS.coh ((Ia Da Da').let₁ hΓ (Ib Db Db')) _ _
  | let₂ hΓ ra rb Ia Ib =>
    have ⟨Da⟩ := ra.wt.left;
    have ⟨Da'⟩ := ra.wt.right;
    have ⟨Db⟩ := rb.wt.left;
    have ⟨Db'⟩ := rb.wt.right;
    exact DRWS.coh ((Ia Da Da').let₂ hΓ (Ib Db Db')) _ _
  | pair hΓ ra rb Ia Ib =>
    have ⟨Da⟩ := ra.wt.left;
    have ⟨Da'⟩ := ra.wt.right;
    have ⟨Db⟩ := rb.wt.left;
    have ⟨Db'⟩ := rb.wt.right;
    exact DRWS.coh ((Ia Da Da').pair hΓ (Ib Db Db')) _ _
  | inl ra Ia =>
    have ⟨Da⟩ := ra.wt.left;
    have ⟨Da'⟩ := ra.wt.right;
    exact DRWS.coh ((Ia Da Da').inl) _ _
  | inr rb Ib =>
    have ⟨Db⟩ := rb.wt.left;
    have ⟨Db'⟩ := rb.wt.right;
    exact DRWS.coh ((Ib Db Db').inr) _ _
  | abort ra Ia =>
    have ⟨Da⟩ := ra.wt.left;
    have ⟨Da'⟩ := ra.wt.right;
    exact DRWS.coh ((Ia Da Da').abort) _ _
  | case hΓ ra rb rc Ia Ib Ic =>
    have ⟨Da⟩ := ra.wt.left;
    have ⟨Da'⟩ := ra.wt.right;
    have ⟨Db⟩ := rb.wt.left;
    have ⟨Db'⟩ := rb.wt.right;
    have ⟨Dc⟩ := rc.wt.left;
    have ⟨Dc'⟩ := rc.wt.right;
    exact DRWS.coh ((Ia Da Da').case hΓ (Ib Db Db') (Ic Dc Dc')) _ _
  | iter hΓ hc hd ra rb Ia Ib =>
    have ⟨Da⟩ := ra.wt.left;
    have ⟨Da'⟩ := ra.wt.right;
    have ⟨Db⟩ := rb.wt.left;
    have ⟨Db'⟩ := rb.wt.right;
    exact DRWS.coh ((Ia Da Da').iter hΓ hc hd (Ib Db Db')) _ _
  | pos_unif hΓ hΓc =>
    apply DRWS.coh
    apply DRWS.uniform.pos_unif hΓ hΓc <;> apply_assumption
  | neg_unif hΓ hΓc =>
    apply DRWS.coh
    apply DRWS.uniform.neg_unif hΓ hΓc <;> apply_assumption
  | base h => exact DRWS.uniform.base h
  | refl => exact DRWS.uniform.refl da db
  | trans ra rb Ia Ib => have ⟨Db⟩ := ra.wt.right; apply DRWS.uniform.trans <;> apply_assumption

theorem DRWS.toRWS_uniform (R : DRWS φ α) : toRWS R.uniform = R.toRWS.uniform := by
  ext Γ A a b
  constructor
  · intro ⟨da, db, h⟩; exact h.toRWS
  · intro h; have ⟨⟨da⟩, ⟨db⟩⟩ := h.wt; exact ⟨_, _, R.uniform_toDRWS_toDWS ▸ h.toDRWS da db⟩

theorem RWS.toDRWS_uniform (R : RWS φ α) : toDRWS R.uniform = R.toDRWS.uniform := by
  ext Γ A a b
  constructor
  · intro h; exact RWS.uniform.toDRWS h _ _
  · intro h; have h' := DRWS.uniform.toRWS h; apply h'.mono; intro _ _ _ _ ⟨_, _, h⟩; exact h

inductive DRWS.symm (R : DRWS φ α) : DRWS φ α
  | fwd {Γ A a b} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} : R.rel da db → symm R _ _ _ _ da db
  | bwd {Γ A a b} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} : R.rel da db → symm R _ _ _ _ db da

inductive DRWS.swap (R : DRWS φ α) : DRWS φ α
  | mk {Γ A a b} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} : R.rel da db → swap R _ _ _ _ db da

inductive DRWS.iso (R : DRWS φ α) : DRWS φ α
  | mk {Γ A a b} {da : Γ ⊢ a : A} {db : Γ ⊢ b : A} : R.rel da db → R.rel db da → iso R _ _ _ _ da db
