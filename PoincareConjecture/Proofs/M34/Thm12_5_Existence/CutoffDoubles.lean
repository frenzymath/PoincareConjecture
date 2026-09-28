import PoincareConjecture.Proofs.M34.Thm12_5_Existence.ModifiedDoubleMetric
import PoincareConjecture.Proofs.M34.Standard.CutoffMetric











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}



theorem cutoffMetric_coefficients_on_truncation (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 3 ≤ R) :
    EqOn (cutoffMetric e h R).euclideanCoefficients h.euclideanCoefficients
      (endTruncation e (R - 1)) := by
  intro x hx
  apply cutoffMetric_coefficients_of_le
  by_cases hc : x ∈ e.carrier
  · have hs := e.inverse_domain x hc
    have hheight : (e.inverse x).2 < R - 1 := by
      apply (endTruncation_coordinate_iff e (by linarith) hs).mp
      simpa only [e.coordinate_right_inverse hc] using hx
    change endExhaustion e x ≤ R
    rw [endExhaustion, if_pos hc]
    have hp := mul_le_mul_of_nonneg_left
      (Real.smoothTransition.le_one ((e.inverse x).2 - 1)) hs
    nlinarith
  · simp only [endExhaustion, if_neg hc]
    linarith



theorem cutoffMetric_coefficients_on_doubleCollar (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 3 ≤ R) :
    EqOn (cutoffMetric e h R).euclideanCoefficients g.euclideanCoefficients
      (endDoubleCollar e (R + 2)) := by
  rintro _ ⟨z, hz, rfl⟩
  apply cutoffMetric_coefficients_of_add_one_le
  rw [endExhaustion_coordinate_of_two_le e (by linarith [hz.2.1])]
  linarith [hz.2.1]



abbrev CutoffDouble (e : StandardCylindricalEnd g) {R : ℝ} (hR : 3 ≤ R) :=
  EndDouble e (by linarith : 1 < R + 2)



noncomputable def cutoffDoubleMetric (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 3 ≤ R) :
    RiemannianMetric 3 (CutoffDouble e hR) :=
  modifiedEndDoubleMetric e (cutoffMetric e h R) (by linarith : 1 < R + 2)
    (cutoffMetric_coefficients_on_doubleCollar e h hR)



noncomputable def cutoffDoubleChart (e : StandardCylindricalEnd g)
    {R : ℝ} (hR : 3 ≤ R) (i : Bool) : StandardCapSpace → CutoffDouble e hR :=
  endDoubleParametrization e (by linarith : 1 < R + 2) i



theorem cutoffDouble_source_subset (e : StandardCylindricalEnd g) (R : ℝ) :
    endTruncation e (R - 1) ⊆ endTruncation e ((R + 2) + 1) :=
  endTruncation_mono e (by linarith)



theorem cutoffDoubleChart_contMDiffOn (e : StandardCylindricalEnd g)
    {R : ℝ} (hR : 3 ≤ R) (i : Bool) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cutoffDoubleChart e hR i) (endTruncation e (R - 1)) :=
  (endDoubleParametrization_contMDiffOn e (by linarith : 1 < R + 2) i).mono
    (cutoffDouble_source_subset e R)



theorem cutoffDoubleChart_mfderiv_isInvertible (e : StandardCylindricalEnd g)
    {R : ℝ} (hR : 3 ≤ R) (i : Bool) {x : StandardCapSpace}
    (hx : x ∈ endTruncation e (R - 1)) :
    (mfderiv (𝓡 3) (𝓡 3) (cutoffDoubleChart e hR i) x).IsInvertible :=
  endDoubleParametrization_mfderiv_isInvertible e (by linarith : 1 < R + 2) i
    (cutoffDouble_source_subset e R hx)



theorem cutoffDoubleMetric_initial_pullback (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 3 ≤ R) (i : Bool)
    {x : StandardCapSpace} (hx : x ∈ endTruncation e (R - 1)) :
    (cutoffDoubleMetric e h hR).pullbackCoefficients (cutoffDoubleChart e hR i) x =
      h.euclideanCoefficients x := by
  ext u v
  have hp := modifiedEndDoubleParametrization_metric e (cutoffMetric e h R)
    (by linarith : 1 < R + 2) (cutoffMetric_coefficients_on_doubleCollar e h hR) i
    (cutoffDouble_source_subset e R hx) u v
  exact hp.symm.trans (congrArg (fun B => B u v)
    (cutoffMetric_coefficients_on_truncation e h hR hx))



theorem cutoffDouble_curvatureDerivative_le (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 3 ≤ R)
    (D : LeviCivitaData (cutoffMetric e h R)) (m : ℕ) {C : ℝ}
    (hbound : ∀ x : StandardCapSpace, D.curvatureDerivativeNorm m x ≤ C)
    (D' : LeviCivitaData (cutoffDoubleMetric e h hR)) (q : CutoffDouble e hR) :
    D'.curvatureDerivativeNorm m q ≤ C :=
  modifiedEndDouble_curvatureDerivative_le e (cutoffMetric e h R) D
    (by linarith : 1 < R + 2) (cutoffMetric_coefficients_on_doubleCollar e h hR)
    m hbound D' q



theorem eventually_compact_subset_cutoff_source (e : StandardCylindricalEnd g)
    {K : Set StandardCapSpace} (hK : IsCompact K) :
    ∀ᶠ k : ℕ in Filter.atTop, K ⊆ endTruncation e ((k : ℝ) + 4) := by
  obtain ⟨R, _hR, hKR⟩ := endTruncation_contains_compact e hK
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [Filter.eventually_ge_atTop N] with k hk
  apply hKR.trans (endTruncation_mono e ?_)
  have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
  linarith

end PoincareConjecture.M34
