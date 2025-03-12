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

inductive DRWS.LetMove : DRWS φ α
  | let_op {f a A B b C}
    (hΓ : Γ.SSplit Γl Γr) (hf : S.FnTy f A B) (Da : Γr ⊢ a : A) (Db : Γl.cons ⟨B, ⊤⟩ ⊢ b : C)
    : LetMove Γ C (.let₁ (.op f a) B b) (.let₁ a A (.let₁ (.op f (.bv 0)) B (↑¹ b)))
      ((Da.op hf).let₁ hΓ Db)
      (Da.let₁ hΓ (.let₁ (Γl.erase_right.cons (.right _))
                  (.op hf (.bv (.here inferInstance (by simp)))) (Db.wk1 _)))
  | let_let₁ {a A b B c C}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (Da : Γr ⊢ a : A) (Db : Γm.cons ⟨A, ⊤⟩ ⊢ b : B) (Dc : Γl.cons ⟨B, ⊤⟩ ⊢ c : C)
    : LetMove Γ C (.let₁ (.let₁ a A b) B c) (.let₁ a A (.let₁ b B (↑¹ c)))
      ((Da.let₁ hΓc Db).let₁ hΓ Dc)
      (Da.let₁ (hΓ.s1_23_12_3 hΓc) (Db.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (Dc.wk1 _)))
  | let_let₂ {a A B b C c D}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (Da : Γr ⊢ a : A.tensor B)
    (Db : (Γm.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b : C) (Dc : Γl.cons ⟨C, ⊤⟩ ⊢ c : D)
    : LetMove Γ D (.let₁ (.let₂ a A B b) C c) (.let₂ a A B (.let₁ b C (↑¹ (↑¹ c))))
      ((Da.let₂ hΓc Db).let₁ hΓ Dc)
      (Da.let₂ (hΓ.s1_23_12_3 hΓc)
          (Db.let₁ (((hΓ.s1_23_12 hΓc).cons (.right _)).cons (.right _)) ((Dc.wk1 _).wk1 _)))
  | let_case {a A B C b c D}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (Da : Γr ⊢ a : A.coprod B) (Db : Γm.cons ⟨A, ⊤⟩ ⊢ b : C) (Dc : Γm.cons ⟨B, ⊤⟩ ⊢ c : C)
    (Dd : Γl.cons ⟨C, ⊤⟩ ⊢ d : D)
    : LetMove Γ D (.let₁ (.case a A B b c) C d) (.case a A B (.let₁ b C (↑¹ d)) (.let₁ c C (↑¹ d)))
      ((Da.case hΓc Db Dc).let₁ hΓ Dd)
      (Da.case (hΓ.s1_23_12_3 hΓc)
      (Db.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (Dd.wk1 _))
      (Dc.let₁ ((hΓ.s1_23_12 hΓc).cons (.right _)) (Dd.wk1 _)))
  | let_abort {a A b B}
    (hΓ : Γ.SSplit Γl Γr) (Da : Γr ⊢ a : Ty.empty) (Db : Γl.cons ⟨A, ⊤⟩ ⊢ b : B)
    : LetMove Γ B (.let₁ (.abort A a) A b) (.let₁ a Ty.empty (.let₁ (.abort A (.bv 0)) A (↑¹ b)))
      (Da.abort.let₁ hΓ Db)
      (Da.let₁ hΓ (.let₁ (Γl.erase_right.cons (.right _))
                  (.abort (.bv (.here inferInstance (by simp)))) (Db.wk1 _)))
  | let_iter {Γ Γc Γl Γm Γr : Ctx? α} {a A B b C}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (hc : Γm.copy) (hd : Γm.del)
    (hcl : Γl.copy) (hdl : Γl.del)
    (Da : Γr ⊢ a : A) (Db : Γm.cons ⟨A, ⊤⟩ ⊢ b : B.coprod A) (Dc : Γl.cons ⟨B, ⊤⟩ ⊢ c : C)
    : LetMove Γ C (.let₁ (.iter a A B b) B c)
                  (.iter a A C (.case b B A (.inl C A (↑¹ c)) (.inr C A (.bv 0))))
      ((Da.iter hΓc hc hd Db).let₁ hΓ Dc)
      (Da.iter (hΓ.s1_23_12_3 hΓc)
              inferInstance
              inferInstance
              (Db.case ((hΓ.s1_23_12 hΓc).cons (.right _))
              (Dc.wk1 ⟨A, 0⟩).inl
              (.inr (.bv (.here inferInstance (by simp))))))

-- Note: let_abort and let_op should be derivable from binding/substitution operators
-- as well as let_inl, let_inr

inductive DRWS.LetBind : DRWS φ α
  | bind_op {f a A B}
    (hf : S.FnTy f A B) (Da : Γ ⊢ a : A)
    : LetBind Γ B _ _ (Da.op hf)
      (Da.let₁ Γ.erase_left (.op hf (.bv (.here inferInstance (by simp)))))
  | bind_let₂ {Γ Γl Γr : Ctx? α} {a A B b C}
    (hΓ : Γ.SSplit Γl Γr) (Da : Γr ⊢ a : A.tensor B) (Db : (Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ b : C)
    : LetBind Γ C _ _ (Da.let₂ hΓ Db)
      (Da.let₁ hΓ
        (.let₂ (Γl.erase_right.cons (.right _))
          .bv0 (Db.wk2 _)))
  | bind_case {Γ Γl Γr : Ctx? α} {a A B b c C}
    (hΓ : Γ.SSplit Γl Γr) (Da : Γr ⊢ a : A.coprod B)
    (Db : Γl.cons ⟨A, ⊤⟩ ⊢ b : C) (Dc : Γl.cons ⟨B, ⊤⟩ ⊢ c : C)
    : LetBind Γ C _ _ (Da.case hΓ Db Dc)
      (Da.let₁ hΓ (.case
        (Γl.erase_right.cons (.right _))
        .bv0 (Db.wk1 _) (Dc.wk1 _)))
  | bind_iter {Γ Γl Γr : Ctx? α} {a A b B}
    (hΓ : Γ.SSplit Γl Γr) (hc : Γl.copy) (hd : Γl.del) (Da : Γr ⊢ a : A)
    (Db : Γl.cons ⟨A, ⊤⟩ ⊢ b : B.coprod A)
    : LetBind Γ B _ _ (Da.iter hΓ hc hd Db)
      (Da.let₁ hΓ (.iter
        (Γl.erase_right.cons (.right _))
        inferInstance
        inferInstance
        .bv0 (Db.wk1 _)))

-- Note: bind_let₁, bind_abort, bind_inl, bind_inr should be derivable from motion/substitution
-- operators

inductive DRWS.Eta : DRWS φ α
  | let₂_eta {Γ : Ctx? α} {a} {A B : Ty α}
    (Da : Γ ⊢ a : A.tensor B) : Eta Γ (A.tensor B) _ _
      (Da.let₂ Γ.erase_left (.pair (((Γ.erase.both).cons (.left _)).cons (.right _)) .bv1 .bv0)) Da
  | case_eta {Γ : Ctx? α} {a} {A B : Ty α}
    (Da : Γ ⊢ a : A.coprod B) : Eta Γ (A.coprod B) _ _
      (Da.case Γ.erase_left (.inl .bv0) (.inr .bv0)) Da

-- Note: let₁_eta should be derivable from substitution operator

inductive DRWS.Beta : DRWS φ α
  | let₂_beta {Γ Γc Γl Γm Γr : Ctx? α} {a A b B c C}
    (hΓ : Γ.SSplit Γl Γc) (hΓc : Γc.SSplit Γm Γr)
    (Da : Γm ⊢ a : A) (Db : Γr ⊢ b : B)
    (Dc : (Γl.cons ⟨A, ⊤⟩).cons ⟨B, ⊤⟩ ⊢ c : C)
    : Beta Γ C _ _
      ((Da.pair hΓc Db).let₂ hΓ Dc)
      (Da.let₁ (hΓ.s1_23_13_2 hΓc)
              ((Db.wk0 _).let₁ ((hΓ.s1_23_13 hΓc).cons (.left _)) Dc))
