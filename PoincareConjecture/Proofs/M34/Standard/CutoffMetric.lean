import PoincareConjecture.Proofs.M34.Standard.EndExhaustion
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.PullbackRicci











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}



noncomputable def endCutoffWeight (e : StandardCylindricalEnd g) (L : ℝ)
    (x : StandardCapSpace) : ℝ :=
  Real.smoothTransition (endExhaustion e x - L)



theorem endCutoffWeight_contDiff (e : StandardCylindricalEnd g) (L : ℝ) :
    ContDiff ℝ ∞ (endCutoffWeight e L) :=
  Real.smoothTransition.contDiff.comp
    ((contMDiff_iff_contDiff.mp (endExhaustion_contMDiff e)).sub contDiff_const)


theorem endCutoffWeight_mem_Icc (e : StandardCylindricalEnd g) (L : ℝ)
    (x : StandardCapSpace) : endCutoffWeight e L x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩



noncomputable def cutoffCoefficients (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) (x : StandardCapSpace) :=
  (1 - endCutoffWeight e L x) • h.euclideanCoefficients x +
    endCutoffWeight e L x • g.euclideanCoefficients x



theorem cutoffCoefficients_contDiff (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) :
    ContDiff ℝ ∞ (cutoffCoefficients e h L) :=
  ((contDiff_const.sub (endCutoffWeight_contDiff e L)).smul
    (show ContDiff ℝ ∞ h.euclideanCoefficients from
      contDiff_iff_contDiffAt.mpr h.contDiffAt_euclideanCoefficients)).add
    ((endCutoffWeight_contDiff e L).smul
      (show ContDiff ℝ ∞ g.euclideanCoefficients from
        contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients))


theorem cutoffCoefficients_symm (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) (x u v : StandardCapSpace) :
    cutoffCoefficients e h L x u v = cutoffCoefficients e h L x v u := by
  change (1 - endCutoffWeight e L x) * h.inner x u v +
    endCutoffWeight e L x * g.inner x u v = _
  rw [h.symm x u v, g.symm x u v]
  rfl



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



noncomputable def cutoffMetric (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) :
    RiemannianMetric 3 StandardCapSpace :=
  RiemannianMetric.ofEuclideanCoefficients (cutoffCoefficients e h L)
    (cutoffCoefficients_contDiff e h L) (cutoffCoefficients_symm e h L)
    (cutoffCoefficients_pos e h L)



theorem cutoffMetric_coefficients (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ) :
    (cutoffMetric e h L).euclideanCoefficients = cutoffCoefficients e h L := rfl



theorem cutoffMetric_coefficients_of_le (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {L : ℝ} {x : StandardCapSpace}
    (hx : endExhaustion e x ≤ L) :
    (cutoffMetric e h L).euclideanCoefficients x = h.euclideanCoefficients x := by
  simp only [cutoffMetric_coefficients, cutoffCoefficients, endCutoffWeight,
    Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx), sub_zero, one_smul,
    zero_smul, add_zero]



theorem cutoffMetric_coefficients_of_add_one_le (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {L : ℝ} {x : StandardCapSpace}
    (hx : L + 1 ≤ endExhaustion e x) :
    (cutoffMetric e h L).euclideanCoefficients x = g.euclideanCoefficients x := by
  simp only [cutoffMetric_coefficients, cutoffCoefficients, endCutoffWeight,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ endExhaustion e x - L),
    sub_self, zero_smul, one_smul, zero_add]



theorem cutoffMetric_pullbackCoefficients (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (L : ℝ)
    (f : StandardCapSpace → StandardCapSpace) (x : StandardCapSpace) :
    (cutoffMetric e h L).pullbackCoefficients f x =
      (1 - endCutoffWeight e L (f x)) • h.pullbackCoefficients f x +
        endCutoffWeight e L (f x) • g.pullbackCoefficients f x := by
  ext u v
  rfl

end PoincareConjecture.M34
