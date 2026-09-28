import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityWeakGreen
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCutoff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Filter
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

theorem disk_green {M : Type*} {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)}
    {U : Set LoopPlane} (F : M65LocalWeakMap e U) (hU : IsOpen U)
    (x : LoopPlane) {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    (hRU : closedBall x R ⊆ U) :
    ∀ᵐ r ∂volume.restrict (Icc ε R),
      ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
        (∫ z in closedBall x r, F.derivative i z j * test z +
          e (F.value z) j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
          r * ∫ θ in (-Real.pi)..Real.pi,
            e (F.value (polarPlane x (r, θ))) j * test (polarPlane x (r, θ)) *
              Proofs.M58.angularPoint θ i := by
  obtain ⟨θ, hc, hs, hθ⟩ := exists_disk_cutoff hU x hR hRU
  have hj (j : Fin N) : ∀ᵐ r ∂volume.restrict (Icc ε R),
      ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
        (∫ z in closedBall x r, F.derivative i z j * test z +
          e (F.value z) j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
          r * ∫ t in (-Real.pi)..Real.pi,
            e (F.value (polarPlane x (r, t))) j * test (polarPlane x (r, t)) *
              Proofs.M58.angularPoint t i := by
    obtain ⟨u, d, hu, hd, hweak⟩ := F.cutoff_global j θ hc hs
    filter_upwards [weakPair_disk_green u d hweak x R hε,
      polar_ae_eq hu x R hε, ae_restrict_mem measurableSet_Icc]
      with r hgreen hcircle hrange
    have hball : closedBall x r ⊆ closedBall x R := closedBall_subset_closedBall hrange.2
    have hcir (t : ℝ) : polarPlane x (r, t) ∈ closedBall x R := by
      change dist (polarPlane x (r, t)) x ≤ R
      rw [dist_eq_norm]
      simp only [polarPlane, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (hε.le.trans hrange.1), Proofs.M58.norm_angularPoint, mul_one]
      exact hrange.2
    intro test i
    calc
      _ = ∫ z in closedBall x r, d i z * test z +
          u z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hu, ae_restrict_of_ae (hd i),
          ae_restrict_mem isClosed_closedBall.measurableSet] with z huz hdz hz
        rw [huz, hdz, (hθ z (hball hz)).2.1, (hθ z (hball hz)).2.2]
        simp only [one_mul, zero_apply, zero_mul, add_zero]
      _ = r * ∫ t in (-Real.pi)..Real.pi,
          u (polarPlane x (r, t)) * test (polarPlane x (r, t)) *
            Proofs.M58.angularPoint t i := hgreen.2 test i
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_ae_restrict
        have hp : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
        rw [uIoc_of_le hp]
        have hslice := ae_restrict_of_ae_restrict_of_subset
          Ioc_subset_Icc_self hcircle
        filter_upwards [hslice] with t ht
        rw [ht, (hθ _ (hcir t)).2.1, one_mul]
  filter_upwards [ae_all_iff.mpr hj] with r hr test i j
  exact hr j test i

end PoincareConjecture.M65LocalWeakMap
