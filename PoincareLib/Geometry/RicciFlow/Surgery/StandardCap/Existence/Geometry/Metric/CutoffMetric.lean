import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Limits.EndExhaustion
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.PullbackRicci

/-!
# Smooth cutoff metrics on the original cap

Interpolate a smooth terminal metric with the original metric using a
translated cutoff of the proper end exhaustion. The interpolation is
positive everywhere, equals the terminal metric below the cutoff, and
equals the original cylinder outside it. This is the compact restart
construction in Morgan-Tian Theorem 12.5, pp. 296-297.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Scalar multiplication acts on nested continuous bilinear-map spaces.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

/-- The original-metric weight, zero on the retained core and one beyond
the unit transition region (Theorem 12.5, pp. 296-297). -/
noncomputable def endCutoffWeight (e : StandardCylindricalEnd g) (L : ℝ)
    (x : StandardCapSpace) : ℝ :=
  Real.smoothTransition (endExhaustion e x - L)

/-- The cutoff is smooth in the original Euclidean coordinates
(Theorem 12.5, pp. 296-297). -/
theorem endCutoffWeight_contDiff (e : StandardCylindricalEnd g) (L : ℝ) :
    ContDiff ℝ ∞ (endCutoffWeight e L) :=
  Real.smoothTransition.contDiff.comp
    ((contMDiff_iff_contDiff.mp (endExhaustion_contMDiff e)).sub contDiff_const)

/-- Both convex weights are nonnegative (Theorem 12.5, pp. 296-297). -/
theorem endCutoffWeight_mem_Icc (e : StandardCylindricalEnd g) (L : ℝ)
    (x : StandardCapSpace) : endCutoffWeight e L x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- Actual bilinear coefficients of the cutoff interpolation
(Theorem 12.5, pp. 296-297). -/
noncomputable def cutoffCoefficients (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) (x : StandardCapSpace) :=
  (1 - endCutoffWeight e L x) • h.euclideanCoefficients x +
    endCutoffWeight e L x • g.euclideanCoefficients x

/-- Smoothness of the actual bilinear interpolation
(Theorem 12.5, pp. 296-297). -/
theorem cutoffCoefficients_contDiff (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) :
    ContDiff ℝ ∞ (cutoffCoefficients e h L) :=
  ((contDiff_const.sub (endCutoffWeight_contDiff e L)).smul
    (show ContDiff ℝ ∞ h.euclideanCoefficients from
      contDiff_iff_contDiffAt.mpr h.contDiffAt_euclideanCoefficients)).add
    ((endCutoffWeight_contDiff e L).smul
      (show ContDiff ℝ ∞ g.euclideanCoefficients from
        contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients))

/-- Symmetry of the convex interpolation (Theorem 12.5, pp. 296-297). -/
theorem cutoffCoefficients_symm (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) (x u v : StandardCapSpace) :
    cutoffCoefficients e h L x u v = cutoffCoefficients e h L x v u := by
  change (1 - endCutoffWeight e L x) * h.inner x u v +
    endCutoffWeight e L x * g.inner x u v = _
  rw [h.symm x u v, g.symm x u v]
  rfl

/-- Positivity holds throughout the entire transition region
(Theorem 12.5, pp. 296-297). -/
theorem cutoffCoefficients_pos (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) (x v : StandardCapSpace)
    (hv : v ≠ 0) : 0 < cutoffCoefficients e h L x v v := by
  have hr := endCutoffWeight_mem_Icc e L x
  have hh := h.pos x v hv
  have hg := g.pos x v hv
  change 0 < (1 - endCutoffWeight e L x) * h.inner x v v +
    endCutoffWeight e L x * g.inner x v v
  rcases lt_or_eq_of_le hr.2 with hlt | heq
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hh)
      (mul_nonneg hr.1 hg.le)
  · rw [heq]
    simpa using hg

/-- A genuine smooth positive cutoff metric on the original cap
(Theorem 12.5, pp. 296-297). -/
noncomputable def cutoffMetric (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) :
    RiemannianMetric 3 StandardCapSpace :=
  RiemannianMetric.ofEuclideanCoefficients (cutoffCoefficients e h L)
    (cutoffCoefficients_contDiff e h L) (cutoffCoefficients_symm e h L)
    (cutoffCoefficients_pos e h L)

/-- The reconstructed metric retains the specified coefficient field
(Theorem 12.5, pp. 296-297). -/
theorem cutoffMetric_coefficients (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) :
    (cutoffMetric e h L).euclideanCoefficients = cutoffCoefficients e h L := rfl

/-- The cutoff metric is exactly the supplied metric on the retained
sublevel, including its boundary (Theorem 12.5, pp. 296-297). -/
theorem cutoffMetric_coefficients_of_le (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {L : ℝ} {x : StandardCapSpace}
    (hx : endExhaustion e x ≤ L) :
    (cutoffMetric e h L).euclideanCoefficients x = h.euclideanCoefficients x := by
  simp only [cutoffMetric_coefficients, cutoffCoefficients, endCutoffWeight,
    Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx), sub_zero, one_smul,
    zero_smul, add_zero]

/-- Outside the transition the metric is exactly the original metric
(Theorem 12.5, pp. 296-297). -/
theorem cutoffMetric_coefficients_of_add_one_le (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {L : ℝ} {x : StandardCapSpace}
    (hx : L + 1 ≤ endExhaustion e x) :
    (cutoffMetric e h L).euclideanCoefficients x = g.euclideanCoefficients x := by
  simp only [cutoffMetric_coefficients, cutoffCoefficients, endCutoffWeight,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ endExhaustion e x - L),
    sub_self, zero_smul, one_smul, zero_add]

/-- Pullback coefficients commute with the pointwise convex interpolation
through the actual differential (Theorem 12.5, pp. 296-297). -/
theorem cutoffMetric_pullbackCoefficients (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ)
    (f : StandardCapSpace → StandardCapSpace) (x : StandardCapSpace) :
    (cutoffMetric e h L).pullbackCoefficients f x =
      (1 - endCutoffWeight e L (f x)) • h.pullbackCoefficients f x +
        endCutoffWeight e L (f x) • g.pullbackCoefficients f x := by
  ext u v
  rfl

end PoincareMT.M34
