import Refinery.Term.Syntax

namespace Refinery

variable {φ : Type u} {α : Type v}

namespace Term

inductive IsExpr : Term φ α → Prop
  | bv (n) : IsExpr .(bv n)
  | op {f a} : IsExpr a → IsExpr (.op f a)
  | unit : IsExpr .unit
  | pair {a b} : IsExpr a → IsExpr b → IsExpr (.pair a b)
  | inl {A B a} : IsExpr a → IsExpr (.inl A B a)
  | inr {A B b} : IsExpr b → IsExpr (.inr A B b)
  | abort {A a} : IsExpr a → IsExpr (.abort A a)
  | invalid : IsExpr .invalid

attribute [class] IsExpr

attribute [simp, instance] IsExpr.bv IsExpr.unit IsExpr.invalid

attribute [simp] IsExpr.pair IsExpr.inl IsExpr.inr IsExpr.abort

instance IsExpr.instOp {f : φ} {a : Term φ α} [ha : IsExpr a] : IsExpr (.op f a) := IsExpr.op ha

instance IsExpr.instPair {a b : Term φ α} [ha : IsExpr a] [hb : IsExpr b] : IsExpr (.pair a b)
  := IsExpr.pair ha hb

instance IsExpr.instInl {A B : α} {a : Term φ α} [ha : IsExpr a] : IsExpr (.inl A B a)
  := IsExpr.inl ha

instance IsExpr.instInr {A B : α} {b : Term φ α} [hb : IsExpr b] : IsExpr (.inr A B b)
  := IsExpr.inr hb

instance IsExpr.instAbort {A : α} {a : Term φ α} [ha : IsExpr a] : IsExpr (.abort A a)
  := IsExpr.abort ha

-- TODO: decision procedure for `IsExpr`

inductive IsVar : Term φ α → Prop
  | bv (n) : IsVar .(bv n)
  | invalid : IsVar .invalid

inductive IsVExpr : Term φ α → Prop
  | var {a} : IsVar a → IsVExpr a
  | op {f a} : IsVar a → IsVExpr (.op f a)
  | unit : IsVExpr .unit
  | pair {a b} : IsVar a → IsVar b → IsVExpr (.pair a b)
  | inl {A B a} : IsVar a → IsVExpr (.inl A B a)
  | inr {A B b} : IsVar b → IsVExpr (.inr A B b)
  | abort {A a} : IsVar a → IsVExpr (.abort A a)
  | invalid : IsVExpr .invalid

inductive IsTuple : Term φ α → Prop
  | bv (n) : IsTuple .(bv n)
  | unit : IsTuple .unit
  | pair {a b} : IsTuple a → IsTuple b → IsTuple (.pair a b)
  | inl {A B a} : IsTuple a → IsTuple (.inl A B a)
  | abort {A a} : IsTuple a → IsTuple (.abort A a)
  | invalid : IsTuple .invalid

inductive IsTExpr : Term φ α → Prop
  | tuple {a} : IsTuple a → IsTExpr a
  | op {f a} : IsTuple a → IsTExpr (.op f a)

inductive IsGANF (P : Term φ α → Prop) : Term φ α → Prop
  | expr {a} : P a → IsGANF P a
  | let₁ {a A b} : P a → IsGANF P b → IsGANF P (.let₁ a A b)
  | let₂ {a A B b} : P a → IsGANF P b → IsGANF P (.let₂ a A B b)
  | case {a A B b c} : P a → IsGANF P b → IsGANF P c → IsGANF P (.case a A B b c)
  | iter {a A B b} : P a → IsGANF P b → IsGANF P (.iter a A B b)

attribute [class] IsGANF

abbrev IsANF : Term φ α → Prop := IsGANF IsExpr

abbrev IsTANF : Term φ α → Prop := IsGANF IsTExpr

abbrev IsVANF : Term φ α → Prop := IsGANF IsVExpr

instance IsANF.instExpr {a : Term φ α} [ha : IsExpr a] : IsANF a := IsGANF.expr ha

instance IsANF.instLet₁ {a : Term φ α} {A : α} {b : Term φ α} [ha : IsExpr a] [hb : IsANF b]
  : IsANF (.let₁ a A b) := IsGANF.let₁ ha hb

instance IsANF.instLet₂ {a : Term φ α} {A B : α} {b : Term φ α} [ha : IsExpr a] [hb : IsANF b]
  : IsANF (.let₂ a A B b) := IsGANF.let₂ ha hb

instance IsANF.instCase {a : Term φ α} {A B : α} {b : Term φ α} {c : Term φ α}
  [ha : IsExpr a] [hb : IsANF b] [hc : IsANF c] : IsANF (.case a A B b c)
  := IsGANF.case ha hb hc

instance IsANF.instIter {a : Term φ α} {A B : α} {b : Term φ α} [ha : IsExpr a] [hb : IsANF b]
  : IsANF (.iter a A B b) := IsGANF.iter ha hb

-- TODO: decision procedure for `IsGANF`
