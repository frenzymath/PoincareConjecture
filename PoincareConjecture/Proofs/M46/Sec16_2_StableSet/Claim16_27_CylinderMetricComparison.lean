import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderMetricSlab
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderMetricLimit
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.FiniteEventInduction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin c : ℝ} {U : Set C.carrier}



theorem cylinderQuadratic_exp_bounds
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin 1 (Icc c 0) U) (hU : IsOpen U)
    {x : C.carrier} (hx : x ∈ U) (v : TangentSpace (𝓡 3) x)
    {a b K : ℝ} (ha : a ∈ Icc c 0) (hb : b ∈ Icc c 0) (hab : a ≤ b)
    (hRm : ∀ t (ht : t ∈ Icc a b),
      (F.connection (origin + t / 1)).curvatureTensorNorm
        (e.forward t (e.interval_connected.out ha hb ht) x) ≤ K) :
    Real.exp (-(6 * K) * (b - a)) * cylinderQuadratic e x v a ≤
        cylinderQuadratic e x v b ∧
      cylinderQuadratic e x v b ≤
        Real.exp ((6 * K) * (b - a)) * cylinderQuadratic e x v a := by
  let events : Set ℝ := (fun t : ℝ => origin + t / 1) ⁻¹' F.surgery_times
  have htime : Icc (origin + a / 1) (origin + b / 1) ⊆ F.time_domain :=
    F.time_domain_interval.out (e.time_subset (mem_image_of_mem _ ha))
      (e.time_subset (mem_image_of_mem _ hb))
  have hfinite : (events ∩ Ioc a b).Finite := by
    have hf := F.surgery_times_finite_on_compact isCompact_Icc htime
    have hinj : Function.Injective (fun t : ℝ => origin + t / 1) := by
      intro s t h
      simpa only [div_one, add_left_cancel_iff] using h
    apply (hf.preimage hinj.injOn).subset
    intro t ht
    refine ⟨ht.1, ?_⟩
    simp only [mem_Icc, div_one]
    constructor <;> linarith [ht.2.1, ht.2.2]
  let Q (t : ℝ) : Prop :=
    Real.exp (-(6 * K) * (t - a)) * cylinderQuadratic e x v a ≤
      cylinderQuadratic e x v t ∧
    cylinderQuadratic e x v t ≤
      Real.exp ((6 * K) * (t - a)) * cylinderQuadratic e x v a
  have hfactor (k s t : ℝ) : Real.exp (k * (t - a)) =
      Real.exp (k * (t - s)) * Real.exp (k * (s - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply finite_event_forward_induction hab hfinite Q (by simp [Q])
  · intro s hs t ht hst hfree hQs
    rcases hst.eq_or_lt with rfl | hst
    · exact hQs
    have hsI := e.interval_connected.out ha hb hs
    have htI := e.interval_connected.out ha hb ht
    have hphysical : Disjoint F.surgery_times (Ioc (origin + s / 1) (origin + t / 1)) := by
      apply Set.disjoint_left.mpr
      intro z hz hzt
      have hp : z - origin ∈ Ioc s t := by
        simp only [div_one] at hzt
        constructor <;> linarith [hzt.1, hzt.2]
      apply Set.disjoint_left.mp hfree _ hp
      simpa only [events, mem_preimage, div_one, add_sub_cancel] using hz
    have hbounds := cylinderQuadratic_exp_bounds_on_slab e hU hx v hsI htI hst hphysical
      (fun z hz => hRm z ⟨hs.1.trans hz.1, hz.2.trans ht.2⟩)
    constructor
    · calc
        _ = Real.exp (-(6 * K) * (t - s)) *
            (Real.exp (-(6 * K) * (s - a)) * cylinderQuadratic e x v a) := by
              rw [hfactor (-(6 * K)) s t, mul_assoc]
        _ ≤ Real.exp (-(6 * K) * (t - s)) * cylinderQuadratic e x v s :=
          mul_le_mul_of_nonneg_left hQs.1 (Real.exp_pos _).le
        _ ≤ _ := hbounds.1
    · calc
        _ ≤ Real.exp ((6 * K) * (t - s)) * cylinderQuadratic e x v s := hbounds.2
        _ ≤ Real.exp ((6 * K) * (t - s)) *
            (Real.exp ((6 * K) * (s - a)) * cylinderQuadratic e x v a) :=
          mul_le_mul_of_nonneg_left hQs.2 (Real.exp_pos _).le
        _ = _ := by rw [hfactor (6 * K) s t]; ring
  · intro t ht hbefore
    have hlimit := cylinderQuadratic_tendsto_left_at_surgery P hpinch e hU hx v
      (show t ∈ Ioc c 0 from ⟨ha.1.trans_lt ht.2.1, ht.2.2.trans hb.2⟩) ht.1
    have hneg : Continuous (fun s : ℝ => Real.exp (-(6 * K) * (s - a)) *
        cylinderQuadratic e x v a) := by fun_prop
    have hpos : Continuous (fun s : ℝ => Real.exp ((6 * K) * (s - a)) *
        cylinderQuadratic e x v a) := by fun_prop
    constructor
    · apply le_of_tendsto_of_tendsto
        (hneg.continuousAt.mono_left nhdsWithin_le_nhds) hlimit
      filter_upwards [Ico_mem_nhdsLT ht.2.1] with s hs
      exact (hbefore s hs).1
    · apply le_of_tendsto_of_tendsto hlimit
        (hpos.continuousAt.mono_left nhdsWithin_le_nhds)
      filter_upwards [Ico_mem_nhdsLT ht.2.1] with s hs
      exact (hbefore s hs).2



theorem cylinderQuadratic_half_le_and_le_double
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin 1 (Icc c 0) U) (hU : IsOpen U)
    {x : C.carrier} (hx : x ∈ U) (v : TangentSpace (𝓡 3) x)
    {K s : ℝ} (hs : s ∈ Icc c 0)
    (hshort : 6 * K * (-s) ≤ 1 / 2)
    (hRm : ∀ t (ht : t ∈ Icc c 0),
      (F.connection (origin + t / 1)).curvatureTensorNorm (e.forward t ht x) ≤ K) :
    cylinderQuadratic e x v 0 / 2 ≤ cylinderQuadratic e x v s ∧
      cylinderQuadratic e x v s ≤ 2 * cylinderQuadratic e x v 0 := by
  have hzero : 0 ∈ Icc c 0 := ⟨hs.1.trans hs.2, le_rfl⟩
  have hbounds := cylinderQuadratic_exp_bounds P hpinch e hU hx v hs hzero hs.2
    (fun t ht => hRm t ⟨hs.1.trans ht.1, ht.2⟩)
  have hn (t : ℝ) (ht : t ∈ Icc c 0) : 0 ≤ cylinderQuadratic e x v t := by
    rw [cylinderQuadratic_of_mem e x v t ht]
    by_cases hv : mfderiv (𝓡 3) (𝓡 3) (e.forward t ht) x v = 0
    · simp [hv]
    · exact ((F.metric (origin + t / 1)).pos _ _ hv).le
  have hpower : 6 * K * (0 - s) ≤ 1 / 2 := by
    simpa only [zero_sub] using hshort
  have hexp : Real.exp (6 * K * (0 - s)) ≤ 2 := by
    apply (Real.exp_le_exp.mpr hpower).trans
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hcancel : Real.exp (6 * K * (0 - s)) *
      Real.exp (-(6 * K) * (0 - s)) = 1 := by
    rw [← Real.exp_add]
    rw [show 6 * K * (0 - s) + -(6 * K) * (0 - s) = 0 by ring, Real.exp_zero]
  have hback := mul_le_mul_of_nonneg_left hbounds.1
    (Real.exp_pos (6 * K * (0 - s))).le
  rw [← mul_assoc, hcancel, one_mul] at hback
  constructor
  · have h := hbounds.2.trans (mul_le_mul_of_nonneg_right hexp (hn s hs))
    linarith
  · exact hback.trans (mul_le_mul_of_nonneg_right hexp (hn 0 hzero))



theorem based_cylinder_metric_comparison_two
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U) (hU : IsOpen U)
    (hbase : ∀ h y, y ∈ U → HEq (e.forward 0 h y) y)
    {x : (F.slice origin).carrier} (hx : x ∈ U) (v : TangentSpace (𝓡 3) x)
    {K s : ℝ} (hs : s ∈ Icc c 0)
    (hshort : 6 * K * (-s) ≤ 1 / 2)
    (hRm : ∀ t (ht : t ∈ Icc c 0),
      (F.connection (origin + t / 1)).curvatureTensorNorm (e.forward t ht x) ≤ K) :
    (F.metric origin).inner x v v ≤
        2 * (F.metric (origin + s / 1)).inner (e.forward s hs x)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) ∧
      (F.metric (origin + s / 1)).inner (e.forward s hs x)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) ≤
        2 * (F.metric origin).inner x v v := by
  classical
  have hzero : 0 ∈ Icc c 0 := ⟨hs.1.trans hs.2, le_rfl⟩
  have hidentity : cylinderQuadratic e x v 0 = (F.metric origin).inner x v v := by
    simp only [cylinderQuadratic, dif_pos hzero]
    rw [surgeryCylinder_pullbackInner_zero hU e hzero (hbase hzero) hx v v, one_mul]
  have h := cylinderQuadratic_half_le_and_le_double P hpinch e hU hx v hs hshort hRm
  rw [hidentity, cylinderQuadratic_of_mem e x v s hs] at h
  exact ⟨by linarith [h.1], h.2⟩

end PoincareConjecture.Proofs.M46
