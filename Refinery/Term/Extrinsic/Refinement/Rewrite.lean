import Refinery.Term.Extrinsic.Refinement.Uniform

namespace Refinery

namespace Term

variable {φ : Type u} {α : Type v} {ε : Type w} [S : Signature φ α ε]

inductive RWS.LetMove : RWS φ α
  | let_op {f a A B b C}
    (hΓ : Γ.SSplit Γl Γr) (hf : S.FnTy f A B) (Da : Γr ⊢ a : A) (Db : Γl.cons ⟨B, ⊤⟩ ⊢ b : C)
    : LetMove Γ C (.let₁ (.op f a) B b) (.let₁ a A (.let₁ (.op f (.bv 0)) B (↑¹ b)))
  | let_let₁ {a A b B c C}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (Da : Γr ⊢ a : A) (Db : Γm.cons ⟨A, ⊤⟩ ⊢ b : B) (Dc : Γl.cons ⟨B, ⊤⟩ ⊢ c : C)
    : LetMove Γ C (.let₁ (.let₁ a A b) B c) (.let₁ a A (.let₁ b B (↑¹ c)))
  | let_let₂ {a A B b C c D}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (Da : Γr ⊢ a : A.tensor B)
    (Db : (Γm.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b : C) (Dc : Γl.cons ⟨C, ⊤⟩ ⊢ c : D)
    : LetMove Γ D (.let₁ (.let₂ a A B b) C c) (.let₂ a A B (.let₁ b C (↑¹ (↑¹ c))))
  | let_case {a A B C b c D}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (Da : Γr ⊢ a : A.coprod B) (Db : Γm.cons ⟨A, ⊤⟩ ⊢ b : C) (Dc : Γm.cons ⟨B, ⊤⟩ ⊢ c : C)
    (Dd : Γl.cons ⟨C, ⊤⟩ ⊢ d : D)
    : LetMove Γ D (.let₁ (.case a A B b c) C d) (.case a A B (.let₁ b C (↑¹ d)) (.let₁ c C (↑¹ d)))
  | let_abort {a A b B}
    (hΓ : Γ.SSplit Γl Γr) (Da : Γr ⊢ a : Ty.empty) (Db : Γl.cons ⟨A, ⊤⟩ ⊢ b : B)
    : LetMove Γ B (.let₁ (.abort A a) A b) (.let₁ a Ty.empty (.let₁ (.abort A (.bv 0)) A (↑¹ b)))
  | let_iter {a A B b C}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (hc : Γm.copy) (hd : Γm.del)
    (hcl : Γl.copy) (hdl : Γl.del)
    (Da : Γr ⊢ a : A) (Db : Γm.cons ⟨A, ⊤⟩ ⊢ b : B.coprod A) (Dc : Γl.cons ⟨B, ⊤⟩ ⊢ c : C)
    : LetMove Γ C (.let₁ (.iter a A B b) B c)
                  (.iter a A C (.case b B A (.inl C A (↑¹ c)) (.inr C A (.bv 0))))

theorem RWS.LetMove.wt {Γ A} {a b : Term φ (Ty α)} (h : LetMove Γ A a b)
  : Term.IsWt Γ A a ∧ Term.IsWt Γ A b := by
  constructor
  · cases h <;> repeat first | assumption | constructor
  cases h with
  | let_op | let_abort =>
    constructor
    constructor
    assumption
    assumption
    constructor
    constructor
    apply Ctx?.erase_right
    apply Var?.SSplit.right
    constructor
    try assumption
    constructor; constructor; infer_instance
    apply Var?.Wk.top_le_one
    apply Deriv.wk1
    assumption
  | let_let₁ hΓ hΓc | let_let₂ hΓ hΓc | let_case hΓ hΓc =>
    constructor
    constructor
    apply Ctx?.SSplit.s1_23_12_3 hΓ hΓc
    repeat assumption
    all_goals {
      repeat first | apply Ctx?.SSplit.s1_23_12 hΓ hΓc | apply Var?.SSplit.right | constructor
      assumption
      repeat apply Deriv.wk1
      assumption
    }
  | let_iter hΓ hΓc hc hd =>
    have hΓl := False
    constructor
    constructor
    apply Ctx?.SSplit.s1_23_12_3 hΓ hΓc
    infer_instance
    infer_instance
    repeat assumption
    repeat first | apply Ctx?.SSplit.s1_23_12 hΓ hΓc | apply Var?.SSplit.right | constructor
    assumption
    constructor
    apply Deriv.wk1
    assumption
    constructor
    constructor
    constructor
    infer_instance
    apply Var?.Wk.top_le_one
