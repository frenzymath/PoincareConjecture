import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.AddCirclePLCharts
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.LocallyPiecewiseAffineInverse

/-!
# Actual short quotient arcs around the circle origin

Restricting the centered quotient chart gives the literal
small real interval and its exact circle image. The inverse
returns the original interval coordinate and retains standard
PL quotient transitions. See Hatcher p. 7, Hamilton 1976,
p. 66 and M76 derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

/-- The actual quotient map restricted to the prescribed
short interval around zero. Its inverse will be the transverse
coordinate of a torus band. See M76 derivation 270. -/
noncomputable def shortArcQuotient (d : ℝ) : OpenPartialHomeomorph ℝ (AddCircle p) :=
  (openPartialHomeomorphCoe p (-p / 2)).restr (Ioo (-d) d)

/-- A radius below half the period gives exactly the stated
open interval as the short quotient-chart source. Empty
intervals are permitted. See M76 derivation 270. -/
theorem shortArcQuotient_source {d : ℝ} (hd : d < p / 2) :
    (shortArcQuotient p d).source = Ioo (-d) d := by
  ext x
  change (x ∈ Ioo (-p / 2) (-p / 2 + p) ∧ x ∈ interior (Ioo (-d) d)) ↔
    x ∈ Ioo (-d) d
  rw [isOpen_Ioo.interior_eq]
  constructor
  · exact And.right
  · intro hx
    exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hx⟩

/-- The short quotient-chart target is its actual circle
arc, including no endpoint classes. See M76 derivation 270. -/
theorem shortArcQuotient_target {d : ℝ} (hd : d < p / 2) :
    (shortArcQuotient p d).target = ((↑) : ℝ → AddCircle p) '' Ioo (-d) d := by
  rw [← (shortArcQuotient p d).image_source_eq_target, shortArcQuotient_source p hd]
  rfl

/-- Inverse short-arc coordinates recover every actual real
representative in the specified interval. See M76 derivation 270. -/
theorem shortArcQuotient_symm_coe {d x : ℝ} (hd : d < p / 2)
    (hx : x ∈ Ioo (-d) d) :
    (shortArcQuotient p d).symm (x : AddCircle p) = x := by
  exact (shortArcQuotient p d).left_inv (by rwa [shortArcQuotient_source p hd])

/-- Every standard quotient chart has PL coordinates in the
short-arc chart, with inverse regularity supplied by the
established local inverse theorem. See Hamilton p. 66 and
M76 derivation 270. -/
theorem shortArcQuotient_transition_mem_piecewiseAffineGroupoid (d a : ℝ) :
    (openPartialHomeomorphCoe p a).trans (shortArcQuotient p d).symm ∈
      piecewiseAffineGroupoid ℝ := by
  let Q := (openPartialHomeomorphCoe p a).trans (shortArcQuotient p d).symm
  apply (mem_piecewiseAffineGroupoid_iff_forward Q).mpr
  have hPL := quotient_chart_transition_locallyPiecewiseAffine p a (-p / 2)
  exact hPL.mono Q.open_source (fun _ hx => ⟨hx.1, hx.2.1⟩)

end AddCircle
