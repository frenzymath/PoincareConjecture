import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Noncollapse
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Gluing



















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

private theorem attached_native_time_mem_half
    {q R M c T a s : ℝ} (hq : 0 < q) (hR : 0 < R) (hM : 0 < M)
    (hc : 0 < c) (hcM : c ≤ 1 / (4 * M)) (hRbound : R ≤ M * q)
    (hac : a ≤ -T + c) (hs : s ∈ Icc (-(T + c)) a) :
    (s - a) * R / q ∈ Icc (-(1 / 2 : ℝ)) 0 := by
  have hcmul : c * (4 * M) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 4 * M)).mp hcM
  have hslope : (a - s) * R ≤ 2 * c * (M * q) := by
    calc
      (a - s) * R ≤ (2 * c) * R :=
        mul_le_mul_of_nonneg_right (by linarith [hs.1]) hR.le
      _ ≤ 2 * c * (M * q) := mul_le_mul_of_nonneg_left hRbound (by positivity)
  have hhalf : 2 * c * (M * q) ≤ q / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hcmul hq.le]
  refine ⟨(le_div_iff₀ hq).mpr ?_,
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.2) hR.le) hq.le⟩
  nlinarith [hslope.trans hhalf]






theorem exists_noncollapsed_cylinder_backward_extension_of_strongNecks
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilonStar K : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧ 0 < K ∧
      ∀ {M B c : ℝ}, 0 < M → 0 ≤ B → K * M ≤ B →
        0 < c → c ≤ 1 / (4 * M) →
      ∀ {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
        {origin q T a : ℝ} {U W : Set C.carrier},
      ∀ (e : GeneralizedFlowCylinder F C origin q (Icc (-T) 0) W),
        IsOpen U → IsOpen W → U.Nonempty → IsCompact (closure U) → closure U ⊆ W →
      ∀ (hTc : c ≤ T) (ha : -T < a) (hac : a ≤ -T + c),
        (∀ s hs x, x ∈ W → F.scalar (e.pointMap s hs x) ≤ M * q) →
        (∀ s hs x, x ∈ W → |F.curvatureNorm (e.pointMap s hs x)| ≤ B * q) →
        (∀ s hs x, x ∈ W → GeneralizedKappaNoncollapsedAt F
          (e.pointMap s hs x) neckNoncollapseConstant 1) →
        (∀ x ∈ closure U, ∃ epsilon, epsilon ≤ epsilonStar ∧
          ∃ N : GeneralizedStrongNeck F (origin + a / q) epsilon,
            N.center = e.forward a ⟨ha.le, by linarith⟩ x) →
        ∃ g : GeneralizedFlowCylinder F C origin q (Icc (-(T + c)) 0) U,
          (∀ s (hs : s ∈ Icc (-T) 0) x, x ∈ U →
            g.pointMap s ⟨by linarith [hs.1], hs.2⟩ x = e.pointMap s hs x) ∧
          (∀ s hs x, x ∈ U → F.scalar (g.pointMap s hs x) ≤ M * q) ∧
          (∀ s hs x, x ∈ U → |F.curvatureNorm (g.pointMap s hs x)| ≤ B * q) ∧
          (∀ s hs x, x ∈ U → GeneralizedKappaNoncollapsedAt F
            (g.pointMap s hs x) neckNoncollapseConstant 1) := by
  obtain ⟨epsilonG, K, hGpos, hGsmall, hK, hglue⟩ :=
    exists_cylinder_backward_extension_of_strongNecks hM04
  obtain ⟨epsilonNC, hNCpos, _hNCsmall, hNC⟩ :=
    exists_strongNeck_backward_center_noncollapsed.{u}
  refine ⟨min epsilonG epsilonNC, K, lt_min hGpos hNCpos,
    (min_le_left _ _).trans hGsmall, hK, ?_⟩
  intro M B c hM hB hKM hc hcM F C origin q T a U W e hU hW hne hcompact hKW
    hTc ha hac hscalar hcurv hnoncollapse hneck
  obtain ⟨g, hgold, hgscalar, hgcurv⟩ := hglue hM hB hKM hc hcM e hU hW hne
    hcompact hKW hTc ha hac hscalar hcurv (fun x hx => by
      obtain ⟨epsilon, hepsilon, N, hcenter⟩ := hneck x hx
      exact ⟨epsilon, hepsilon.trans (min_le_left _ _), N, hcenter⟩)
  refine ⟨g, hgold, hgscalar, hgcurv, ?_⟩
  intro s hs x hx
  have hxW : x ∈ W := hKW (subset_closure hx)
  by_cases hsOld : -T ≤ s
  · have hso : s ∈ Icc (-T) 0 := ⟨hsOld, hs.2⟩
    rw [hgold s hso x hx]
    exact hnoncollapse s hso x hxW
  · have hsa : s ≤ a := by linarith
    have ha0 : a ≤ 0 := by linarith
    have haOld : a ∈ Icc (-T) 0 := ⟨ha.le, ha0⟩
    obtain ⟨epsilon, hepsilon, N, hcenter⟩ := hneck x (subset_closure hx)
    have hRbound : N.scale⁻¹ ^ 2 ≤ M * q := by
      have hscale : N.scale =
          (Real.sqrt ((F.connection (origin + a / q)).scalarCurvature N.center))⁻¹ := by
        rw [N.scale_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le,
          Real.sqrt_eq_rpow]
      rw [hscale, inv_inv, Real.sq_sqrt N.scalar_center_pos.le, hcenter]
      exact hscalar a haOld x hxW
    have hnativeHalf : ∀ r ∈ Icc (-(T + c)) a,
        (r - a) * (N.scale⁻¹ ^ 2) / q ∈ Icc (-(1 / 2 : ℝ)) 0 :=
      fun r hr => attached_native_time_mem_half e.scale_pos
        (sq_pos_of_pos (inv_pos.mpr N.scale_pos)) hM hc hcM hRbound hac hr
    have hnative : ∀ r ∈ Icc (-(T + c)) a,
        (r - a) * (N.scale⁻¹ ^ 2) / q ∈ Ioc (-1) 0 := by
      intro r hr
      exact ⟨lt_of_lt_of_le (by norm_num) (hnativeHalf r hr).1, (hnativeHalf r hr).2⟩
    let V := W ∩ (e.forward a haOld) ⁻¹' N.carrier
    let d : GeneralizedFlowCylinder F C origin q (Icc (-(T + c)) a) V :=
      strongNeckAttachedCylinder e hW haOld N hnative
    have hxV : x ∈ V := by
      refine ⟨hxW, ?_⟩
      change e.forward a haOld x ∈ N.carrier
      rw [← hcenter]
      exact N.central_sphere_subset N.center_on_central_sphere
    have haPatch : a ∈ Icc (-(T + c)) a := ⟨by linarith, le_rfl⟩
    have haNew : a ∈ Icc (-(T + c)) 0 := ⟨by linarith, ha0⟩
    have hdanchor : d.pointMap a haPatch x = e.pointMap a haOld x := by
      rw [strongNeckAttachedCylinder_pointMap]
      have hid (r : ℝ) (hr : r ∈ Ioc (-1) 0) (hr0 : r = 0) :
          N.time_cylinder.pointMap r hr (e.forward a haOld x) = e.pointMap a haOld x := by
        subst r
        change N.time_cylinder.pointMap 0 hr (e.forward a haOld x) =
          (⟨origin + a / q, e.forward a haOld x⟩ : F.point)
        exact N.cylinder_identity hr (e.forward a haOld x) hxV.2
      exact hid _ _ (by ring)
    have hanchor : g.pointMap a haNew x = d.pointMap a haPatch x :=
      (hgold a haOld x hx).trans hdanchor.symm
    have hsame := cylinder_pointMap_eq_on_overlap g d ordConnected_Icc ordConnected_Icc
      hx hxV haNew haPatch hanchor s hs ⟨hs.1, hsa⟩
    rw [hsame, strongNeckAttachedCylinder_pointMap, ← hcenter]
    exact hNC N (hepsilon.trans (min_le_right _ _))
      (hnative s ⟨hs.1, hsa⟩) (hnativeHalf s ⟨hs.1, hsa⟩).1

end PoincareConjecture.M32
