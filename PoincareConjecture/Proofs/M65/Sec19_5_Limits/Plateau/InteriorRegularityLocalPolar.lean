import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarACL
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCutoff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology SchwartzMap

namespace PoincareConjecture.M65LocalWeakMap

open M65Interior

private theorem polar_ae_eq {f g : LoopPlane → ℝ} (hfg : f =ᵐ[volume] g)
    (x : LoopPlane) {ε : ℝ} (R : ℝ) (hε : 0 < ε) :
    ∀ᵐ r ∂volume.restrict (Icc ε R),
      (fun t => f (polarPlane x (r, t))) =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
        fun t => g (polarPlane x (r, t)) := by
  have hp : ∀ᵐ p ∂(volume.restrict (Icc ε R)).prod
      (volume.restrict (Icc (-Real.pi) Real.pi)), f (polarPlane x p) = g (polarPlane x p) :=
    ae_of_ae_map (polarPlane_measurePreserving x).measurable.aemeasurable
      (ae_mono (polarPlane_map_strip_le x hε)
        (Measure.ae_smul_measure hfg (ENNReal.ofReal ε)⁻¹))
  exact Measure.ae_ae_of_ae_prod hp

theorem polar_coordinate_AC {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (hU : IsOpen U) (x : LoopPlane)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (hRU : closedBall x R ⊆ U) (j : Fin N) :
    ∀ᵐ r ∂volume.restrict (Icc ε R),
      MemLp (fun t => -r * Real.sin t * F.derivative 0 (polarPlane x (r, t)) j +
        r * Real.cos t * F.derivative 1 (polarPlane x (r, t)) j) 2
          (volume.restrict (Icc (-Real.pi) Real.pi)) ∧
      ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v (-Real.pi) Real.pi ∧
        (v =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
          fun t => e (F.value (polarPlane x (r, t))) j) ∧
        v (-Real.pi) = v Real.pi ∧
        ∀ s ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
          v t - v s = ∫ θ in s..t,
            -r * Real.sin θ * F.derivative 0 (polarPlane x (r, θ)) j +
              r * Real.cos θ * F.derivative 1 (polarPlane x (r, θ)) j := by
  obtain ⟨θ, hc, hs, hθ⟩ := exists_disk_cutoff hU x hR hRU
  obtain ⟨u, d, hu, hd, hweak⟩ := F.cutoff_global j θ hc hs
  have hAC := weakPair_polar_AC u d hweak x R hε
  filter_upwards [hAC, polar_ae_eq hu x R hε,
    polar_ae_eq (hd 0) x R hε, polar_ae_eq (hd 1) x R hε,
    ae_restrict_mem measurableSet_Icc] with r hr hur hd0 hd1 hrange
  have hcircle (t : ℝ) : polarPlane x (r, t) ∈ closedBall x R := by
    change dist (polarPlane x (r, t)) x ≤ R
    rw [dist_eq_norm]
    simp only [polarPlane, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hε.le.trans hrange.1), Proofs.M58.norm_angularPoint, mul_one]
    exact hrange.2
  have hu' : (fun t => u (polarPlane x (r, t))) =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => e (F.value (polarPlane x (r, t))) j := by
    filter_upwards [hur] with t ht
    rw [ht, (hθ _ (hcircle t)).2.1, one_mul]
  have hd' :
      (fun t => -r * Real.sin t * d 0 (polarPlane x (r, t)) +
        r * Real.cos t * d 1 (polarPlane x (r, t))) =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
      fun t => -r * Real.sin t * F.derivative 0 (polarPlane x (r, t)) j +
        r * Real.cos t * F.derivative 1 (polarPlane x (r, t)) j := by
    filter_upwards [hd0, hd1] with t h0 h1
    rw [h0, h1, (hθ _ (hcircle t)).2.1, (hθ _ (hcircle t)).2.2]
    simp only [one_mul, zero_apply, zero_mul, add_zero]
  obtain ⟨hm, v, hv, hvu, hvp, hvi⟩ := hr
  refine ⟨hm.ae_eq hd', v, hv, hvu.trans hu', hvp, ?_⟩
  intro s hs t ht
  rw [hvi s hs t ht]
  apply intervalIntegral.integral_congr_ae_restrict
  exact ae_restrict_of_ae_restrict_of_subset
    (uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)) hd'

end PoincareConjecture.M65LocalWeakMap
