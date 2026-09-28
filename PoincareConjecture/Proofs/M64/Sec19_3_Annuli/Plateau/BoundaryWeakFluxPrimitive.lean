import PoincareConjecture.Proofs.M08.WeakMomentum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularSlice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology ContDiff intervalIntegral

namespace PoincareConjecture

theorem m64WeakGreen_zero_boundary_primitive
    {P Q : ℝ → ℝ} (hP : IntegrableOn P (Icc (0 : ℝ) 1) volume)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) 1) volume)
    (hgreen : ∀ phi : ℝ → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      (∫ s in Icc (0 : ℝ) 1, deriv phi s * P s) +
        (∫ s in Icc (0 : ℝ) 1, phi s * Q s) = 0) :
    ContinuousOn (fun s => ∫ x in (0 : ℝ)..s, Q x) (Icc (0 : ℝ) 1) ∧
      (∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), P s = ∫ x in (0 : ℝ)..s, Q x) ∧
      (∫ x in (0 : ℝ)..1, Q x) = 0 := by
  have hp : IntervalIntegrable P volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hP
  have hq : IntervalIntegrable Q volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hQ
  obtain ⟨c, hc⟩ := M08.weak_momentum_primitive (by norm_num : (0 : ℝ) < 1) P Q hp hq
    (by
      intro phi hphi hcompact _
      have hg := hgreen phi hphi hcompact
      simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
        smul_eq_mul] at hg ⊢
      linarith)
  let H := fun s : ℝ => c + ∫ x in (0 : ℝ)..s, Q x
  have hI := hq.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 1 :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  have hH : AbsolutelyContinuousOnInterval H 0 1 := hconst.add hI
  have hboundary (phi : ℝ → ℝ) (hphi : ContDiff ℝ ∞ phi) (hcompact : HasCompactSupport phi) :
      H 1 * phi 1 - H 0 * phi 0 = 0 := by
    have hphiAC : AbsolutelyContinuousOnInterval phi 0 1 :=
      (hphi.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
    have hi := hH.integral_mul_deriv_eq_deriv_mul hphiAC
    have hd : (∫ s in (0 : ℝ)..1, deriv H s * phi s) =
        ∫ s in (0 : ℝ)..1, Q s * phi s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hq.ae_hasDerivAt_integral] with s hs hmem
      exact congrArg (fun z => z * phi s)
        (((hs (uIoc_subset_uIcc hmem) 0 left_mem_uIcc).const_add c).deriv)
    rw [hd] at hi
    simp only [intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc] at hi
    have hleft : (∫ s in Icc (0 : ℝ) 1, H s * deriv phi s) =
        ∫ s in Icc (0 : ℝ) 1, deriv phi s * P s := by
      apply integral_congr_ae
      filter_upwards [hc] with s hs
      rw [hs]
      exact mul_comm _ _
    rw [hleft] at hi
    have hright : (∫ s in Icc (0 : ℝ) 1, Q s * phi s) =
        ∫ s in Icc (0 : ℝ) 1, phi s * Q s := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => mul_comm _ _
    rw [hright] at hi
    linarith [hgreen phi hphi hcompact]
  let bump : ContDiffBump (0 : ℝ) := ⟨2, 3, by norm_num, by norm_num⟩
  have hb0 : bump 0 = 1 := bump.one_of_mem_closedBall (by
    change dist (0 : ℝ) 0 ≤ 2
    norm_num)
  have hb1 : bump 1 = 1 := bump.one_of_mem_closedBall (by
    change dist (1 : ℝ) 0 ≤ 2
    norm_num [Real.dist_eq])
  have hz := hboundary (fun s => bump s * (1 - s))
    (bump.contDiff.mul (contDiff_const.sub contDiff_id)) bump.hasCompactSupport.mul_right
  have h1 := hboundary (fun s => bump s * s)
    (bump.contDiff.mul contDiff_id) bump.hasCompactSupport.mul_right
  simp only [hb0, hb1, sub_self, mul_zero, sub_zero, mul_one, zero_sub] at hz h1
  have hc0 : c = 0 := by
    simpa only [H, intervalIntegral.integral_same, add_zero] using neg_eq_zero.mp hz
  refine ⟨?_, ?_, ?_⟩
  · simpa only [uIcc_of_le zero_le_one] using hI.continuousOn
  · simpa only [hc0, zero_add] using hc
  · simpa only [H, hc0, zero_add] using h1

end PoincareConjecture
