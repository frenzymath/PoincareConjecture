import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.CenteredTorusSquareChart

/-!
# Pulling a quotient-coordinate PL map into the centered square

The centered square is a translation followed by the actual
standard product quotient chart. Hence locally PL formulas in
that quotient chart pull back to its full centered domain.
See Hamilton 1976, p. 66 and M76 derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace AddCircle

/-- A map locally PL in the actual standard product quotient
chart is locally PL in the whole centered square chart.
The source is the exact inverse image of its specified target
region. See Hamilton p. 66 and M76 derivation 270. -/
theorem locallyPiecewiseAffineOn_comp_centeredSquareQuotient
    (p : ℝ) [Fact (0 < p)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (AddCircle p × AddCircle p) → F) (U : Set (AddCircle p × AddCircle p))
    (hf : let T := (openPartialHomeomorphCoe p 0).prod (openPartialHomeomorphCoe p 0)
      LocallyPiecewiseAffineOn (f ∘ T) (T.source ∩ T ⁻¹' U)) :
    LocallyPiecewiseAffineOn (f ∘ centeredSquareQuotient p)
      ((centeredSquareQuotient p).source ∩ centeredSquareQuotient p ⁻¹' U) := by
  let A := ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (p / 2, p / 2)
  let T := (openPartialHomeomorphCoe p 0).prod (openPartialHomeomorphCoe p 0)
  have hA : LocallyPiecewiseAffineOn A (univ : Set (ℝ × ℝ)) :=
    locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ
  have hcomp := hf.comp hA
  change LocallyPiecewiseAffineOn ((f ∘ T) ∘ A)
    ((univ ∩ A ⁻¹' T.source) ∩ (fun x => T (A x)) ⁻¹' U)
  convert hcomp using 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_univ, true_and]
  rfl

end AddCircle
