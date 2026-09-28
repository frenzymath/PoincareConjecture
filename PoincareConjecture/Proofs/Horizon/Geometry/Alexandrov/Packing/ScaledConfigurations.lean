import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.SmallScale
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.FiniteMovingPoints










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.GromovHausdorff

namespace Poincare.Alexandrov

universe u



theorem exists_pos_radius_for_scaled_configurations
    {θ β : ℝ} (hθ : 0 < θ) (hθβ : θ < β) (hβpi : β < Real.pi) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
        {Y : FiniteDiameterBasedMetricSpace.{u}}
        (_S : VaryingRealizationSequence
          (fun j => (X j).toBasedMetricSpaceBundle) Y.toBasedMetricSpaceBundle)
        {R σ : ℝ}, 0 < R → R < R₀ → R < σ →
        IsCompact (Metric.closedBall Y.base σ) →
        ∀ {k : ℕ} (x : ∀ j, Fin k → (X j).carrier),
          (∀ j i, dist (X j).base (x j i) = R) →
          ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝 0) →
          (∀ᶠ j in atTop, t j ≠ 0) →
          (∀ᶠ j in atTop, ∀ i l : Fin k, i ≠ l →
            β ≤ comparisonAngle (t j * dist (X j).base (x j i))
              (t j * dist (X j).base (x j l)) (t j * dist (x j i) (x j l))) →
          ∃ q : Fin k → Y.carrier, (∀ i, dist Y.base (q i) = R) ∧
            ∀ i l : Fin k, i ≠ l →
              θ < comparisonAngle (dist Y.base (q i)) (dist Y.base (q l))
                (dist (q i) (q l)) := by
  obtain ⟨R₀, hR₀, hsmall⟩ :=
    exists_pos_comparisonAngle_gt_of_euclidean_angle_ge hθ hθβ hβpi
  refine ⟨R₀, hR₀, ?_⟩
  intro X Y S R σ hR hRR₀ hRσ hcompact k x hx t ht htne hangle
  obtain ⟨q, _, φ, hφ, hq⟩ :=
    exists_subseq_finite_pointConverges S hRσ hcompact x (fun j i => (hx j i).le)
  let S' := S.comp φ hφ.tendsto_atTop
  have hradconv (i : Fin k) : Tendsto
      (fun j => dist (X (φ j)).base (x (φ j) i)) atTop (𝓝 R) := by
    simpa only [hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => R) atTop (𝓝 R))
  have hrad (i : Fin k) : dist Y.base (q i) = R :=
    tendsto_nhds_unique
      (S'.tendsto_dist_base (fun j => x (φ j) i) (q i) (hq i)) (hradconv i)
  refine ⟨q, hrad, ?_⟩
  intro i l hil
  have hdist := S'.tendsto_dist_of_pointConverges (hq i) (hq l)
  have hscaled := tendsto_comparisonAngle_mul_of_tendsto_zero
    (ht.comp hφ.tendsto_atTop) (hφ.tendsto_atTop.eventually htne)
    (hradconv i) (hradconv l) hdist hR hR
  have heuc : β ≤ Real.arccos ((2 * R ^ 2 - dist (q i) (q l) ^ 2) / (2 * R ^ 2)) := by
    have hbound : β ≤ Real.arccos
        ((R ^ 2 + R ^ 2 - dist (q i) (q l) ^ 2) / (2 * R * R)) := by
      apply ge_of_tendsto hscaled
      filter_upwards [hφ.tendsto_atTop.eventually hangle] with j hj
      exact hj i l hil
    convert hbound using 1
    congr 1
    ring
  rw [hrad i, hrad l]
  apply hsmall R (dist (q i) (q l)) hR hRR₀ dist_nonneg ?_ heuc
  calc
    dist (q i) (q l) ≤ dist (q i) Y.base + dist Y.base (q l) := dist_triangle _ _ _
    _ = 2 * R := by rw [dist_comm (q i), hrad i, hrad l]; ring

end Poincare.Alexandrov
