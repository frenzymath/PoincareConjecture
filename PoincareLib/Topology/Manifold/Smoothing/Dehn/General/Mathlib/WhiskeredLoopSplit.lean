import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Based class of a literal closed-subwalk split

The retained whisker reaches the actual current vertex. Splitting
off a closed middle path gives two loops at the original basepoint,
in Mathlib's reversed multiplication order. See Stallings, section
2.A.2, p. 11, and Dehn derivation 024, section 3.
-/

set_option autoImplicit false

namespace Path

variable {X : Type*} [TopologicalSpace X] {b v w : X}

/-- The class at the original basepoint obtained using the actual
path to the loop basepoint. See Dehn 024, section 3. -/
noncomputable def whiskeredLoopClass (p : Path b v) (q : Path v v) :
    FundamentalGroup X b :=
  FundamentalGroup.fromPath (Homotopic.Quotient.mk ((p.trans q).trans p.symm))

/-- A constant middle loop gives the identity at the original
basepoint, for every actual whisker. See Dehn 024, section 3. -/
theorem whiskeredLoopClass_refl (p : Path b v) :
    p.whiskeredLoopClass (Path.refl v) = 1 := by
  change ((Homotopic.Quotient.mk p).trans (Homotopic.Quotient.refl v)).trans
    (Homotopic.Quotient.mk p).symm = Homotopic.Quotient.refl b
  rw [Homotopic.Quotient.trans_refl, Homotopic.Quotient.trans_symm]

/-- The actual closed-middle-path split, with both factors still
based at the original point. Multiplication reverses geometric
concatenation order. See Stallings p. 11 and Dehn 024, section 3. -/
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

/-- If the original closed walk is excluded, one of the two actual
shorter loops remains excluded with its retained whisker. This step
needs only subgroup closure. See Dehn 024, section 3. -/
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
