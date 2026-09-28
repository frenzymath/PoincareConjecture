import PoincareConjecture.Proofs.M60.Mathlib.LogLaplacian
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundGreen
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundVolume
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.LocalFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped Manifold ContDiff

namespace PoincareConjecture

theorem m60RoundSphere_curvature_integral_of_differential_inequality
    (D : LeviCivitaData m60RoundSphereMetric) {q k : UnitTwoSphere → ℝ}
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hnonneg : ∀ p, 0 ≤ q p)
    (hpos : ∀ᵐ p ∂m60RoundSphereMetric.volumeMeasure, 0 < q p)
    (hk : Integrable k m60RoundSphereMetric.volumeMeasure)
    (hreg : ∀ p, 0 < q p →
      M04.scalarGradientSq m60RoundSphereMetric q p / q p + 2 * q p -
        2 * q p * k p ≤ D.laplacian q p) :
    4 * Real.pi ≤ ∫ p, k p ∂m60RoundSphereMetric.volumeMeasure := by
  rw [← m60RoundSphereMetric_volume_univ]
  apply M60.measure_le_integral_of_regularized_ratios hq.continuous.aemeasurable hpos hk
  intro ε he
  let r : UnitTwoSphere → ℝ := fun p => q p / (q p + ε)
  have hden (p : UnitTwoSphere) : 0 < q p + ε :=
    add_pos_of_nonneg_of_pos (hnonneg p) he
  have hr : Continuous r := hq.continuous.div (hq.continuous.add continuous_const)
    (fun p => (hden p).ne')
  have hr0 (p : UnitTwoSphere) : 0 ≤ r p := div_nonneg (hnonneg p) (hden p).le
  have hr1 (p : UnitTwoSphere) : r p ≤ 1 :=
    (div_le_one (hden p)).mpr (le_add_of_nonneg_right he.le)
  have hri : Integrable r m60RoundSphereMetric.volumeMeasure :=
    hr.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hki : Integrable (fun p => r p * k p) m60RoundSphereMetric.volumeMeasure :=
    hk.bdd_mul hr.aestronglyMeasurable (Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (hr0 p)]
      exact hr1 p)
  have hlog : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p => Real.log (q p + ε)) := by
    intro p
    exact (Real.contDiffAt_log.mpr (hden p).ne').contMDiffAt.comp p
      ((hq p).add contMDiffAt_const)
  obtain ⟨hLi, hL0⟩ := m60RoundSphere_integral_laplacian D _ hlog
  have hi := integral_mono ((hri.const_mul 2).sub (hki.const_mul 2)) hLi
    (fun p => show 2 * r p - 2 * (r p * k p) ≤
      D.laplacian (fun y => Real.log (q y + ε)) p from by
        convert! M60.laplacian_log_add_lower_bound D hq hnonneg hreg he p using 1
        dsimp [r]
        ring)
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (hri.const_mul 2) (hki.const_mul 2),
    integral_const_mul, integral_const_mul, hL0] at hi
  change (∫ p, r p ∂m60RoundSphereMetric.volumeMeasure) ≤
    ∫ p, r p * k p ∂m60RoundSphereMetric.volumeMeasure
  linarith

end PoincareConjecture
