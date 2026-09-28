import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.AnnulusApproximation

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X ι : Type*} [MetricSpace X] {p : X}

theorem tendsto_normalized_radius_of_annulusConeRelation (hcomparison : RayComparison p)
    {l : Filter ι} {L τ : ι → ℝ} {x : ι → X}
    {z : ι → AsymptoticCone p hcomparison} {z₀ : AsymptoticCone p hcomparison}
    (hL : ∀ᶠ k in l, 0 < L k)
    (hrel : ∀ᶠ k in l, annulusConeRelation hcomparison (L k) (τ k) (x k) (z k))
    (hz : Tendsto z l (𝓝 z₀)) :
    Tendsto (fun k => dist p (x k) / L k) l
      (𝓝 (asymptoticConeRadius hcomparison z₀ : ℝ)) := by
  have hcont : Continuous (fun w : AsymptoticCone p hcomparison =>
      (asymptoticConeRadius hcomparison w : ℝ)) :=
    NNReal.continuous_coe.comp (lipschitzWith_asymptoticConeRadius hcomparison).continuous
  apply ((hcont.tendsto z₀).comp hz).congr'
  filter_upwards [hL, hrel] with k hk hr
  exact annulusConeRelation_radius hcomparison hk hr

theorem cone_radial_potential_eq_of_annulusConeRelation (hcomparison : RayComparison p)
    {l : Filter ι} [l.NeBot] {L τ : ι → ℝ} {x : ι → X}
    {z : ι → AsymptoticCone p hcomparison} {z₀ : AsymptoticCone p hcomparison} {v : ℝ}
    (hL : ∀ᶠ k in l, 0 < L k)
    (hrel : ∀ᶠ k in l, annulusConeRelation hcomparison (L k) (τ k) (x k) (z k))
    (hz : Tendsto z l (𝓝 z₀))
    (hpotential : Tendsto (fun k => (dist p (x k) / L k) ^ 2 / 2) l (𝓝 v)) :
    (asymptoticConeRadius hcomparison z₀ : ℝ) ^ 2 / 2 = v :=
  tendsto_nhds_unique
    ((tendsto_normalized_radius_of_annulusConeRelation hcomparison hL hrel hz).pow 2 |>.div_const 2)
    hpotential

theorem dist_unit_cone_lt_of_annulusConeRelation_ray (hcomparison : RayComparison p)
    (η : basedMinimizingRays p) {L τ : ℝ} (hL : 0 < L)
    {z : AsymptoticCone p hcomparison}
    (hrel : annulusConeRelation hcomparison L τ (rayExtension η L) z) :
    dist z (asymptoticConeRayProjection hcomparison (1, η)) < τ := by
  have hradial : dist p (rayExtension η L) = L := by
    simpa only [rayExtension_zero, zero_sub, abs_neg, abs_of_pos hL] using
      rayExtension_dist η (le_refl 0) hL.le
  obtain ⟨γ, hγ, hnear⟩ := hrel
  rw [hradial, div_self hL.ne', Real.toNNReal_one] at hγ
  rw [hradial] at hnear
  rw [← hγ]
  have hbound := cone_distance_le_rescaled_ray_distance hcomparison γ η 1 1 hL
  simp only [NNReal.coe_one, one_mul] at hbound
  exact hbound.trans_lt (by simpa only [dist_comm] using hnear)

theorem tendsto_unit_cone_of_annulusConeRelation_ray (hcomparison : RayComparison p)
    (η : basedMinimizingRays p) {l : Filter ι} {L τ : ι → ℝ}
    {z : ι → AsymptoticCone p hcomparison}
    (hL : ∀ᶠ k in l, 0 < L k) (hτ : Tendsto τ l (𝓝 0))
    (hrel : ∀ᶠ k in l,
      annulusConeRelation hcomparison (L k) (τ k) (rayExtension η (L k)) (z k)) :
    Tendsto z l (𝓝 (asymptoticConeRayProjection hcomparison (1, η))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hL, hrel, hτ.eventually_lt_const hε] with k hk hr hsmall
  exact (dist_unit_cone_lt_of_annulusConeRelation_ray hcomparison η hk hr).trans hsmall

end Poincare.AncientVolume.ScalarRatio
