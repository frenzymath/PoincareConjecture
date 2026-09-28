import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.SmallScale
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.FiniteMovingPoints

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.GromovHausdorff

namespace Poincare.Alexandrov

universe u

theorem exists_pos_radius_for_scaled_moving_configurations
    {θ β : ℝ} (hθ : 0 < θ) (hθβ : θ < β) (hβpi : β < Real.pi) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
        {Y : FiniteDiameterBasedMetricSpace.{u}}
        (S : VaryingRealizationSequence
          (fun j => (X j).toBasedMetricSpaceBundle) Y.toBasedMetricSpaceBundle)
        {u : ∀ j, (X j).carrier} {u0 : Y.carrier}, S.PointConverges u u0 →
        ∀ {R ρ σ : ℝ}, 0 < R → R < R₀ → ρ + R < σ →
        IsCompact (Metric.closedBall Y.base σ) →
        (∀ᶠ j in atTop, dist (X j).base (u j) ≤ ρ) →
        ∀ {k : ℕ} (x : ∀ j, Fin k → (X j).carrier),
          (∀ j i, dist (u j) (x j i) = R) →
          ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝 0) →
          (∀ᶠ j in atTop, t j ≠ 0) →
          (∀ᶠ j in atTop, ∀ i l : Fin k, i ≠ l →
            β ≤ comparisonAngle (t j * dist (u j) (x j i))
              (t j * dist (u j) (x j l)) (t j * dist (x j i) (x j l))) →
          ∃ q : Fin k → Y.carrier, (∀ i, dist u0 (q i) = R) ∧
            ∀ i l : Fin k, i ≠ l →
              θ < comparisonAngle (dist u0 (q i)) (dist u0 (q l))
                (dist (q i) (q l)) := by
  obtain ⟨R₀, hR₀, hsmall⟩ :=
    exists_pos_comparisonAngle_gt_of_euclidean_angle_ge hθ hθβ hβpi
  refine ⟨R₀, hR₀, ?_⟩
  intro X Y S u u0 hu R ρ σ hR hRR₀ hroom hcompact hubound k x hx t ht htne hangle
  obtain ⟨η, hη, hηbound⟩ := Filter.extraction_of_frequently_atTop hubound.frequently
  let Sη := S.comp η hη.tendsto_atTop
  have hbound (j : ℕ) (i : Fin k) :
      dist (X (η j)).base (x (η j) i) ≤ ρ + R := by
    calc
      dist (X (η j)).base (x (η j) i) ≤
          dist (X (η j)).base (u (η j)) + dist (u (η j)) (x (η j) i) :=
        dist_triangle _ _ _
      _ = dist (X (η j)).base (u (η j)) + R := by rw [hx]
      _ ≤ ρ + R := add_le_add (hηbound j) le_rfl
  obtain ⟨q, _, φ, hφ, hq⟩ :=
    exists_subseq_finite_pointConverges Sη hroom hcompact (fun j => x (η j)) hbound
  let S' := Sη.comp φ hφ.tendsto_atTop
  have hu' : S'.PointConverges (fun j => u (η (φ j))) u0 :=
    (hu.comp η hη.tendsto_atTop).comp φ hφ.tendsto_atTop
  have hcofinal : Tendsto (fun j => η (φ j)) atTop atTop :=
    hη.tendsto_atTop.comp hφ.tendsto_atTop
  have hradconv (i : Fin k) : Tendsto
      (fun j => dist (u (η (φ j))) (x (η (φ j)) i)) atTop (𝓝 R) := by
    simpa only [hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => R) atTop (𝓝 R))
  have hrad (i : Fin k) : dist u0 (q i) = R :=
    tendsto_nhds_unique (S'.tendsto_dist_of_pointConverges hu' (hq i)) (hradconv i)
  refine ⟨q, hrad, ?_⟩
  intro i l hil
  have hdist := S'.tendsto_dist_of_pointConverges (hq i) (hq l)
  have hscaled := tendsto_comparisonAngle_mul_of_tendsto_zero
    (ht.comp hcofinal) (hcofinal.eventually htne)
    (hradconv i) (hradconv l) hdist hR hR
  have heuc : β ≤ Real.arccos ((2 * R ^ 2 - dist (q i) (q l) ^ 2) / (2 * R ^ 2)) := by
    have hbound : β ≤ Real.arccos
        ((R ^ 2 + R ^ 2 - dist (q i) (q l) ^ 2) / (2 * R * R)) := by
      apply ge_of_tendsto hscaled
      filter_upwards [hcofinal.eventually hangle] with j hj
      exact hj i l hil
    convert hbound using 1
    congr 1
    ring
  rw [hrad i, hrad l]
  apply hsmall R (dist (q i) (q l)) hR hRR₀ dist_nonneg ?_ heuc
  calc
    dist (q i) (q l) ≤ dist (q i) u0 + dist u0 (q l) := dist_triangle _ _ _
    _ = 2 * R := by rw [dist_comm (q i), hrad i, hrad l]; ring

end Poincare.Alexandrov
