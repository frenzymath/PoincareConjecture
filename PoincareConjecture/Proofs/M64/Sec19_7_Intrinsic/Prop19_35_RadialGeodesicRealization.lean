import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MetricGerm
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegularExponential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64Intrinsic_unit_geodesic_radial_realization
    (G : RiemannianMetric 2 AnnulusCoordinates)
    (L : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates)
    {e : AnnulusCoordinates → AnnulusCoordinates} {p : AnnulusCoordinates} {R : ℝ}
    (hL : ∀ v w, G.inner p (L v) (L w) = inner ℝ v w)
    (he0 : e 0 = p) (hed : HasFDerivAt e L.toContinuousLinearMap 0)
    (hradial : ∀ v ∈ ball 0 R, G.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ ball 0 R})
    {q : ℝ → AnnulusCoordinates} (hq : ContDiff ℝ ∞ q) {T : ℝ}
    (hT : 0 < T) (hTR : T < R) (hq0 : q 0 = p)
    (hgeo : G.IsGeodesicOn q (Icc 0 T))
    (hunit : G.inner (q 0) (deriv q 0) (deriv q 0) = 1) :
    ∃ v : AnnulusCoordinates, ‖v‖ = T ∧ v ∈ ball 0 R ∧
      ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) = q (T * t) := by
  let v : AnnulusCoordinates := L.symm (T • deriv q 0)
  have hLv : L v = T • deriv q 0 := L.apply_symm_apply _
  have hnorm : ‖v‖ = T := by
    have h := hL v v
    rw [← hq0, hLv] at h
    simp only [map_smul, smul_apply, smul_eq_mul, hunit,
      real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg v]
  have hv : v ∈ ball 0 R := by simpa only [mem_ball, dist_zero_right, hnorm] using hTR
  have hrad : G.IsGeodesicOn (fun t : ℝ => e (t • v)) (Icc 0 1) := by
    intro t ht
    apply hradial v hv t
    rw [mem_ofPred_eq, mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt
      (by simpa only [one_mul, hnorm] using hTR)
  have hscaled : G.IsGeodesicOn (fun t : ℝ => q (T * t)) (Icc 0 1) := by
    intro t ht
    apply hgeo.comp_mul T t
    exact ⟨mul_nonneg hT.le ht.1,
      (mul_le_mul_of_nonneg_left ht.2 hT.le).trans_eq (mul_one T)⟩
  have hdr : HasDerivAt (fun t : ℝ => e (t • v)) (L v) 0 := by
    have hs : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa only [one_smul, id_eq] using! (hasDerivAt_id (0 : ℝ)).smul_const v
    exact (show HasFDerivAt e L.toContinuousLinearMap ((0 : ℝ) • v) from
      by simpa only [zero_smul] using hed).comp_hasDerivAt 0 hs
  have hdq : HasDerivAt (fun t : ℝ => q (T * t)) (T • deriv q 0) 0 := by
    have hs : HasDerivAt (fun t : ℝ => T * t) T 0 := by
      simpa only [mul_one, id_eq] using! (hasDerivAt_id (0 : ℝ)).const_mul T
    simpa only [mul_zero, Function.comp_apply] using!
      ((hq.differentiable (by simp) (T * 0)).hasDerivAt.scomp 0 hs)
  have hvel : deriv (fun t : ℝ => e (t • v)) 0 =
      deriv (fun t : ℝ => q (T * t)) 0 := hdr.deriv.trans (hLv.trans hdq.deriv.symm)
  have heq := hrad.eq_nhds_of_initial_data hscaled
    (show (0 : ℝ) ∈ Icc 0 1 from by norm_num) p (by simp)
    (by simpa only [zero_smul, mul_zero] using he0.trans hq0.symm)
    (by simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using hvel)
  exact ⟨v, hnorm, hv, fun t ht => hrad.eqOn_of_eq_nhds hscaled
    (convex_Icc (0 : ℝ) 1).isPreconnected (by norm_num) heq ht⟩

end PoincareConjecture
