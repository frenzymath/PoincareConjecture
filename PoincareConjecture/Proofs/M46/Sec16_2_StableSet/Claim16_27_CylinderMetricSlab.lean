import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderMetric
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.M04.TensorNormBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem cylinderQuadratic_exp_bounds_on_slab
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin 1 I U) (hU : IsOpen U)
    {x : C.carrier} (hx : x ∈ U) (v : TangentSpace (𝓡 3) x)
    {a b K : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a < b)
    (hfree : Disjoint F.surgery_times (Ioc (origin + a / 1) (origin + b / 1)))
    (hRm : ∀ t (ht : t ∈ Icc a b),
      (F.connection (origin + t / 1)).curvatureTensorNorm
        (e.forward t (e.interval_connected.out ha hb ht) x) ≤ K) :
    Real.exp (-(6 * K) * (b - a)) * cylinderQuadratic e x v a ≤
        cylinderQuadratic e x v b ∧
      cylinderQuadratic e x v b ≤
        Real.exp ((6 * K) * (b - a)) * cylinderQuadratic e x v a := by
  have hab' : origin + a / 1 < origin + b / 1 := by
    simpa only [div_one] using add_lt_add_right hab origin
  have hparam (t : ℝ) (ht : t ∈ Icc (origin + a / 1) (origin + b / 1)) :
      ∃ s ∈ Icc a b, origin + s / 1 = t := by
    refine ⟨t - origin, ?_, by simp⟩
    simp only [div_one] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hJ : Icc (origin + a / 1) (origin + b / 1) ⊆ F.time_domain := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := hparam t ht
    exact e.time_subset (mem_image_of_mem _ (e.interval_connected.out ha hb hs))
  let S := F.regular_slabs _ _ hab' hJ hfree
  let f := (S.identify ⟨origin + a / 1, ⟨le_rfl, hab'.le⟩⟩).symm ∘ e.forward a ha
  let V := mfderiv (𝓡 3) (𝓡 3) f x v
  have hRic (t : ℝ) (ht : t ∈ Icc (origin + a / 1) (origin + b / 1)) :
      |(S.flow.connection t).ricci (f x) V V| ≤ (3 * K) * (S.flow.metric t).inner (f x) V V := by
    obtain ⟨s, hs, rfl⟩ := hparam t ht
    have hsI := e.interval_connected.out ha hb hs
    have hmap := e.slab_compatibility _ _ hab' hJ hfree a ha s hsI
      ⟨le_rfl, hab'.le⟩ ht x hx
    change S.identify ⟨origin + s / 1, ht⟩ (f x) = e.forward s hsI x at hmap
    have hnorm := M13.homothety_curvatureTensorNorm_eq
      (S.flow.metric (origin + s / 1)) (F.metric (origin + s / 1))
      (S.identify ⟨origin + s / 1, ht⟩) 1 zero_lt_one
      (M44.regularSlab_metricHomothety F S ⟨origin + s / 1, ht⟩)
      (S.flow.connection (origin + s / 1)) (F.connection (origin + s / 1)) (f x)
    have hcurvature := hRm s hs
    rw [← hmap, hnorm, div_one] at hcurvature
    have hq : 0 ≤ (S.flow.metric (origin + s / 1)).inner (f x) V V := by
      by_cases hV : V = 0
      · simp [hV]
      · exact ((S.flow.metric (origin + s / 1)).pos (f x) V hV).le
    have h := (M04.abs_ricci_le_curvatureTensorNorm
      (S.flow.connection (origin + s / 1)) (f x) V).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcurvature
          (by norm_num : (0 : ℝ) ≤ 3)) hq)
    simpa only [Nat.cast_ofNat] using h
  have hbounds := S.flow.metric_inner_self_exp_bounds (convex_Icc _ _) (Subset.refl _)
    (f x) V (3 * K) hRic ⟨le_rfl, hab'.le⟩ ⟨hab'.le, le_rfl⟩
  rw [cylinderQuadratic_eq_slab e hU hx v hab' hJ hfree a a ha ha
    ⟨le_rfl, hab'.le⟩ ⟨le_rfl, hab'.le⟩,
    cylinderQuadratic_eq_slab e hU hx v hab' hJ hfree a b ha hb
      ⟨le_rfl, hab'.le⟩ ⟨hab'.le, le_rfl⟩]
  have hconstant : 2 * (3 * K) = 6 * K := by ring
  simpa only [div_one, add_sub_add_left_eq_sub,
    abs_of_nonneg (sub_nonneg.mpr hab.le), hconstant] using hbounds

end PoincareConjecture.Proofs.M46
