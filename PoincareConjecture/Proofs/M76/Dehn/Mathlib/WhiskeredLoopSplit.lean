import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

set_option autoImplicit false

namespace Path

variable {X : Type*} [TopologicalSpace X] {b v w : X}

noncomputable def whiskeredLoopClass (p : Path b v) (q : Path v v) :
    FundamentalGroup X b :=
  FundamentalGroup.fromPath (Homotopic.Quotient.mk ((p.trans q).trans p.symm))

theorem whiskeredLoopClass_refl (p : Path b v) :
    p.whiskeredLoopClass (Path.refl v) = 1 := by
  change ((Homotopic.Quotient.mk p).trans (Homotopic.Quotient.refl v)).trans
    (Homotopic.Quotient.mk p).symm = Homotopic.Quotient.refl b
  rw [Homotopic.Quotient.trans_refl, Homotopic.Quotient.trans_symm]

theorem whiskeredLoopClass_split (p : Path b v) (a : Path v w)
    (q : Path w w) (c : Path w v) :
    p.whiskeredLoopClass ((a.trans q).trans c) =
      p.whiskeredLoopClass (a.trans c) * (p.trans a).whiskeredLoopClass q := by
  simp only [whiskeredLoopClass, FundamentalGroup.mul_def, Path.trans_symm,
    Homotopic.Quotient.mk_trans, Homotopic.Quotient.mk_symm,
    Homotopic.Quotient.trans_assoc]
  rw [← Homotopic.Quotient.trans_assoc
      (Homotopic.Quotient.mk p).symm (Homotopic.Quotient.mk p),
    Homotopic.Quotient.symm_trans, Homotopic.Quotient.refl_trans,
    ← Homotopic.Quotient.trans_assoc
      (Homotopic.Quotient.mk a).symm (Homotopic.Quotient.mk a),
    Homotopic.Quotient.symm_trans, Homotopic.Quotient.refl_trans]

theorem whiskeredLoopClass_split_excluded
    (J : Subgroup (FundamentalGroup X b)) (p : Path b v) (a : Path v w)
    (q : Path w w) (c : Path w v)
    (h : p.whiskeredLoopClass ((a.trans q).trans c) ∉ J) :
    (p.trans a).whiskeredLoopClass q ∉ J ∨ p.whiskeredLoopClass (a.trans c) ∉ J := by
  classical
  by_cases hq : (p.trans a).whiskeredLoopClass q ∈ J
  · right
    intro hc
    apply h
    rw [whiskeredLoopClass_split]
    exact J.mul_mem hc hq
  · exact Or.inl hq

end Path
