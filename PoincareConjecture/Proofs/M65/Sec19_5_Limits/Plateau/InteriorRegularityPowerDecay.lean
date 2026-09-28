import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEnergyInequality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Interior

theorem ac_radial_power_decay {E : ℝ → ℝ} {r R K : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hK : 0 < K)
    (hE : AbsolutelyContinuousOnInterval E r R)
    (hineq : ∀ᵐ s ∂volume.restrict (Ioo r R), E s ≤ K * s * deriv E s) :
    E r ≤ E R * (r / R) ^ K⁻¹ := by
  have hR : 0 < R := hr.trans_le hrR
  let w (s : ℝ) := s ^ (-K⁻¹)
  have hw : ContDiffOn ℝ 1 w (uIcc r R) := by
    apply contDiffOn_id.rpow_const_of_ne
    intro s hs
    exact (hr.trans_le (uIcc_of_le hrR ▸ hs).1).ne'
  have hprod := hE.fun_mul hw.absolutelyContinuousOnInterval
  have hineqcc : ∀ᵐ s ∂volume.restrict (Icc r R), E s ≤ K * s * deriv E s := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hineq
  have hnonneg : ∀ᵐ s ∂volume.restrict (Icc r R),
      0 ≤ deriv (fun t => E t * w t) s := by
    filter_upwards [hineqcc, ae_restrict_of_ae hE.ae_differentiableAt,
      ae_restrict_mem measurableSet_Icc] with s hi hs hsmem
    have hs0 : 0 < s := hr.trans_le hsmem.1
    have hsu : s ∈ uIcc r R := by simpa only [uIcc_of_le hrR] using hsmem
    have hd := (hs hsu).hasDerivAt.mul
      (Real.hasDerivAt_rpow_const (p := -K⁻¹) (Or.inl hs0.ne'))
    change 0 ≤ deriv (E * fun t => t ^ (-K⁻¹)) s
    rw [hd.deriv, Real.rpow_sub_one hs0.ne']
    have hi' : K⁻¹ * E s ≤ s * deriv E s := by
      have h := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hK.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul] using h
    have hsign := mul_nonneg
      (div_nonneg (Real.rpow_nonneg hs0.le (-K⁻¹)) hs0.le) (sub_nonneg.mpr hi')
    calc
      0 ≤ (s ^ (-K⁻¹) / s) * (s * deriv E s - K⁻¹ * E s) := hsign
      _ = _ := by
        rw [mul_sub, ← mul_assoc, div_mul_cancel₀ _ hs0.ne']
        ring
  have hi := intervalIntegral.integral_nonneg_of_ae_restrict hrR hnonneg
  rw [hprod.integral_deriv_eq_sub] at hi
  have hmono : E r * w r ≤ E R * w R := sub_nonneg.mp hi
  have hpow : 0 < r ^ K⁻¹ := Real.rpow_pos_of_pos hr _
  calc
    E r = (E r * w r) * r ^ K⁻¹ := by
      dsimp only [w]
      rw [mul_assoc, Real.rpow_neg hr.le, inv_mul_cancel₀ hpow.ne', mul_one]
    _ ≤ (E R * w R) * r ^ K⁻¹ := mul_le_mul_of_nonneg_right hmono hpow.le
    _ = E R * (r / R) ^ K⁻¹ := by
      dsimp only [w]
      rw [Real.div_rpow hr.le hR.le, Real.rpow_neg hR.le]
      ring

theorem localMinimum_energy_power_decay
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (E0 : ℝ) (hE0 : 0 ≤ E0) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      ∀ (U : Set LoopPlane) (F : M65LocalWeakMap e U), IsOpen U →
        M65LocallyMinimizesEnergy g F → ∀ (x : LoopPlane) (r R : ℝ),
          0 < r → r ≤ R → closedBall x R ⊆ U →
          (∫ z in closedBall x R, m65EmbeddedEnergyDensity g e F.value F.derivative z) ≤ E0 →
          (∫ z in closedBall x r, m65EmbeddedEnergyDensity g e F.value F.derivative z) ≤
            E0 * (r / R) ^ a := by
  obtain ⟨K, hK, hbound⟩ :=
    localMinimum_radial_energy_inequality g e he hinj hemb compact E0 hE0
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨K⁻¹, inv_pos.mpr hKpos, ?_, ?_⟩
  · exact (inv_le_one₀ hKpos).mpr hK
  intro U F hU hmin x r R hr hrR hRU htotal
  have hR : 0 < R := hr.trans_le hrR
  rcases hrR.eq_or_lt with rfl | hrR
  · simpa only [div_self hr.ne', Real.one_rpow, mul_one] using htotal
  let E (s : ℝ) := ∫ z in closedBall x s,
    m65EmbeddedEnergyDensity g e F.value F.derivative z
  have hE : AbsolutelyContinuousOnInterval E r R :=
    (F.energy_radial g he hinj hemb compact x hR hRU).1.mono (by
      rw [uIcc_of_le hrR.le, uIcc_of_le hR.le]
      exact Icc_subset_Icc hr.le le_rfl)
  have hdecay := ac_radial_power_decay hr hrR.le hKpos hE
    (hbound U F hU hmin x r R hr hrR hRU htotal)
  exact hdecay.trans (mul_le_mul_of_nonneg_right htotal
    (Real.rpow_nonneg (div_nonneg hr.le hR.le) _))

end PoincareConjecture.M65Interior
