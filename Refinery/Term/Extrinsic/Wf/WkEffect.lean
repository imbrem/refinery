import Refinery.Term.Extrinsic.Wf.Effect
import Refinery.Term.Extrinsic.Wf.Wk

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable  {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε] {R : DRWS φ α}

def Wf.HasEff.wk {Γ Δ : Ctx? α} {A : Ty α} {a : Wf R Δ A} (e : ε) (ρ : Γ.Wk Δ) (ha : a.HasEff e)
  : (a.wk ρ).HasEff e := Term.HasEff.instWk ρ

instance Wf.HasEff.instWk {Γ Δ : Ctx? α} {A : Ty α} (ρ : Γ.Wk Δ) (a : Wf R Δ A) (e : ε)
  [ha : a.HasEff e] : (a.wk ρ).HasEff e := ha.wk e ρ

def Wf.HasEff.wk0
  {Γ : Ctx? α} {A : Ty α} {a : Wf R Γ A} (e : ε) (x : Var? α) [hx : x.del] (ha : a.HasEff e)
  : (a.wk0 x (hv := hx)).HasEff e := Term.HasEff.instWk _

def Wf.HasEff.wk1
  {Γ : Ctx? α} {v : Var? α} {A : Ty α} {a : Wf R (Γ.cons v) A} (e : ε) (x : Var? α) [hx : x.del]
  (ha : a.HasEff e) : (a.wk1 x (hv := hx)).HasEff e := Term.HasEff.instWk _

def Wf.HasEff.wk2
  {Γ : Ctx? α} {l r : Var? α} {A : Ty α} {a : Wf R ((Γ.cons l).cons r) A} (e : ε) (x : Var? α)
  [hx : x.del] (ha : a.HasEff e) : (a.wk2 x (h := hx)).HasEff e := Term.HasEff.instWk _

instance Wf.HasEff.instWk0
  {Γ : Ctx? α} {A : Ty α} (x : Var? α) (hx : x.del) (a : Wf R Γ A) (e : ε)
  [ha : a.HasEff e] : (a.wk0 x).HasEff e := ha.wk0 e x

instance Wf.HasEff.instWk1
  {Γ : Ctx? α} {v : Var? α} {A : Ty α} (x : Var? α) (hx : x.del) (a : Wf R (Γ.cons v) A) (e : ε)
  [ha : a.HasEff e] : (a.wk1 x).HasEff e := ha.wk1 e x

instance Wf.HasEff.instWk2
  {Γ : Ctx? α} {l r : Var? α} {A : Ty α} (x : Var? α) (hx : x.del)
  (a : Wf R ((Γ.cons l).cons r) A) (e : ε)
  [ha : a.HasEff e] : (a.wk2 x).HasEff e := ha.wk2 e x
