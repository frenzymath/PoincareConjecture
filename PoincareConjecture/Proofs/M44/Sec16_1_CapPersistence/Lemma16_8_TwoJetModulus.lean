import PoincareConjecture.Proofs.M44.Mathlib.SpatialJetNorms
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarJet










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

noncomputable local instance twoJetCoefficientNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricCoefficient n) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance twoJetCoefficientNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricCoefficient n) := ContinuousLinearMap.toNormedSpace

noncomputable local instance twoJetNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricTwoJet n) := Prod.normedAddCommGroup

noncomputable local instance twoJetNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricTwoJet n) := Prod.normedSpace




theorem norm_metricTwoJet_sub_le {n : ℕ} (B A : E n → MetricCoefficient n)
    (x : E n) {L : ℝ}
    (h : ∀ j ≤ 2, ‖iteratedFDeriv ℝ j B x - iteratedFDeriv ℝ j A x‖ ≤ L) :
    ‖metricTwoJet B x - metricTwoJet A x‖ ≤ L := by
  change max ‖B x - A x‖ (max ‖fderiv ℝ B x - fderiv ℝ A x‖
    ‖fderiv ℝ (fderiv ℝ B) x - fderiv ℝ (fderiv ℝ A) x‖) ≤ L
  apply max_le
  · rw [← norm_iteratedFDeriv_zero_sub]
    exact h 0 (by omega)
  · apply max_le
    · rw [norm_fderiv_sub_eq_jet]
      exact h 1 (by omega)
    · rw [norm_fderiv_sub_eq_jet, norm_iteratedFDeriv_fderiv_sub]
      exact h 2 le_rfl




theorem metricTwoJet_time_modulus {n : ℕ} (B : ℝ → E n → MetricCoefficient n)
    (x : E n) {s t L : ℝ}
    (h : ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (B t) x - iteratedFDeriv ℝ j (B s) x‖ ≤
      L * |t - s|) :
    ‖metricTwoJet (B t) x - metricTwoJet (B s) x‖ ≤ L * |t - s| :=
  norm_metricTwoJet_sub_le _ _ x h

end PoincareConjecture.M44
