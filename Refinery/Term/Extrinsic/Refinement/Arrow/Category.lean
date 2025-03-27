import Refinery.Term.Extrinsic.Wf.Wk

open HasQuant HasPQuant HasCommRel

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

set_option linter.unusedVariables false in
def DRWS.Obj (R : DRWS φ α) := Ty α

def DRWS.PreArrow (R : DRWS φ α) (A B : Ty α) : Type _ := Wf R (.one ⟨A, ⊤⟩) B

instance DRWS.PreArrow.instPreorder
  (R : DRWS φ α) (A B : Ty α) : Preorder (DRWS.PreArrow R A B)
  := Wf.instPreorder R _ _

instance DRWS.PreArrow.setoid (R : DRWS φ α) (A B : Ty α) : Setoid (DRWS.PreArrow R A B)
  := Wf.setoid R _ _

def DRWS.Arrow (R : DRWS φ α) (A B : Ty α) : Type _ := Eqv R (.one ⟨A, ⊤⟩) B

instance DRWS.Arrow.instPartialOrder
  (R : DRWS φ α) (A B : Ty α) : PartialOrder (DRWS.Arrow R A B)
  := Eqv.instPartialOrder R _ _

variable {R : DRWS φ α}

def DRWS.PreArrow.toWf (a : DRWS.PreArrow R A B) : Wf R (.one ⟨A, ⊤⟩) B := a

def DRWS.PreArrow.extend1 (Γ : Ctx? α) [hΓ : Γ.del] (a : DRWS.PreArrow R A B)
  : Wf R (Γ.cons ⟨A, ⊤⟩) B := a.toWf.wk (Γ.extend1 ⟨A, ⊤⟩)

def DRWS.PreArrow.e (a : DRWS.PreArrow R A B) : Arrow R A B := e⟦a⟧

def DRWS.PreArrow.refl (R : DRWS φ α) (A : Ty α) : PreArrow R A A := Wf.bv0

def Wf.letPreArrow {Γ : Ctx? α} {A B : Ty α} (a : Wf R Γ A) (b : R.PreArrow A B) : Wf R Γ B
  := a.let₁ Γ.erase_left (b.extend1 Γ.erase)

def DRWS.PreArrow.comp {A B C : Ty α} (g : DRWS.PreArrow R B C) (f : DRWS.PreArrow R A B)
  : DRWS.PreArrow R A C := Wf.letPreArrow f g

--TODO: comp_congr

--TODO: comp_id

--TODO: id_comp

--TODO: comp_assoc

def DRWS.Arrow.refl (R : DRWS φ α) (A : Ty α) : Arrow R A A := (PreArrow.refl R A).e

--TODO: DRWS.Arrow.comp

--TODO: DRWS.Arrow is a category!

--TODO: then
-- monoidal category structure
--
