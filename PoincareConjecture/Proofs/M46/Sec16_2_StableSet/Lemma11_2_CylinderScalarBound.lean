import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CylinderScalarContinuity
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_FiniteScalarComparison
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CanonicalAnalytics
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveCylinderLines

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin c : ℝ} {U : Set C.carrier}

theorem cylinderScalar_le_four_inv_sq
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin 1 (Icc c 0) U)
    {x : C.carrier} (hx : x ∈ U) (hc : c ≤ 0) {B r : ℝ}
    (hB : 0 < B) (hr : 0 < r)
    (hinitial : cylinderScalar e x 0 ≤ 2 * r⁻¹ ^ 2)
    (hrate : ∀ s ∈ Ioo c 0, origin + s / 1 ∉ F.surgery_times →
      r⁻¹ ^ 2 ≤ cylinderScalar e x s →
        |cylinderScalarRate e x s| ≤ B * cylinderScalar e x s ^ 2)
    (hshort : 64 * B * r⁻¹ ^ 2 * (-c) ≤ 1) :
    ∀ s ∈ Icc c 0, cylinderScalar e x s ≤ 4 * r⁻¹ ^ 2 := by
  let f : ℝ → ℝ := fun t => cylinderScalar e x (-t)
  let rate : ℝ → ℝ := fun t => -cylinderScalarRate e x (-t)
  let events : Set ℝ := (fun t : ℝ => origin - t) ⁻¹' F.surgery_times
  have htime : Icc (origin + c) origin ⊆ F.time_domain := by
    apply F.time_domain_interval.out
    · simpa only [div_one] using
        e.time_subset (mem_image_of_mem _ (show c ∈ Icc c 0 from ⟨le_rfl, hc⟩))
    · simpa only [zero_div, add_zero] using
        e.time_subset (mem_image_of_mem _ (show 0 ∈ Icc c 0 from ⟨hc, le_rfl⟩))
  have hfinite : (events ∩ Ioc 0 (-c)).Finite := by
    have hf := F.surgery_times_finite_on_compact isCompact_Icc htime
    have hinj : Function.Injective (fun t : ℝ => origin - t) := fun _ _ h => by linarith
    apply (hf.preimage hinj.injOn).subset
    intro t ht
    exact ⟨ht.1, by dsimp only [mem_Icc]; constructor <;> linarith [ht.2.1, ht.2.2]⟩
  have hcont : ContinuousOn f (Icc 0 (-c)) :=
    (cylinderScalar_continuousOn P hpinch e hx).comp
      continuous_neg.continuousOn (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hderiv : ∀ t ∈ Ioo 0 (-c), t ∉ events → HasDerivAt f (rate t) t := by
    intro t ht hnot
    have hs : -t ∈ Ioo c 0 := by constructor <;> linarith [ht.1, ht.2]
    have hnot' : origin + -t / 1 ∉ F.surgery_times := by
      simpa only [events, mem_preimage, div_one, sub_eq_add_neg] using hnot
    have h := (cylinderScalar_hasDerivAt_of_not_surgery P e hx hs hnot').comp t
      (hasDerivAt_neg t)
    simpa only [f, rate, Function.comp_def, div_one, mul_neg_one] using h
  have hrate' : ∀ t ∈ Ioo 0 (-c), t ∉ events →
      r⁻¹ ^ 2 ≤ f t → rate t ≤ B * f t ^ 2 := by
    intro t ht hnot hhigh
    have hs : -t ∈ Ioo c 0 := by constructor <;> linarith [ht.1, ht.2]
    have hnot' : origin + -t / 1 ∉ F.surgery_times := by
      simpa only [events, mem_preimage, div_one, sub_eq_add_neg] using hnot
    exact (neg_le_abs _).trans (hrate (-t) hs hnot' hhigh)
  have hbound := scalar_le_four_inv_sq_of_finite_events hB hr hfinite hcont hderiv
    (by simpa only [f, neg_zero] using hinitial) hrate' hshort
  intro s hs
  simpa only [f, neg_neg] using hbound (-s) (by constructor <;> linarith [hs.1, hs.2])

theorem canonical_cylinderScalar_le_four_inv_sq
    (P : M44CapPersistencePredecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin 1 (Icc c 0) U)
    {x : C.carrier} (hx : x ∈ U) (hc : c ≤ 0) {B r : ℝ}
    (hB : seedAnalyticConstant S ≤ B) (hr : 0 < r)
    (hpositive : ¬ SurgeryPositiveComponentAt F (origin + 0 / 1)
      (e.forward 0 ⟨hc, le_rfl⟩ x))
    (hinitial : cylinderScalar e x 0 ≤ 2 * r⁻¹ ^ 2)
    (hcanonical : ∀ s (hs : s ∈ Ioo c 0), origin + s / 1 ∉ F.surgery_times →
      r⁻¹ ^ 2 ≤ cylinderScalar e x s →
        SurgeryCanonicalControl F (origin + s / 1)
          (e.forward s (Ioo_subset_Icc_self hs) x) F.parameters.epsilon S.setup.C)
    (hshort : 64 * B * r⁻¹ ^ 2 * (-c) ≤ 1) :
    ∀ s ∈ Icc c 0, cylinderScalar e x s ≤ 4 * r⁻¹ ^ 2 := by
  apply cylinderScalar_le_four_inv_sq P hpinch e hx hc
    ((seedAnalyticConstant_pos S).trans_le hB) hr hinitial _ hshort
  intro s hs hnot hhigh
  have hnonpositive : ¬ SurgeryPositiveComponentAt F (origin + s / 1)
      (e.forward s (Ioo_subset_Icc_self hs) x) := by
    intro hpos
    exact hpositive (positive_component_cylinder_line e hx (Ioo_subset_Icc_self hs)
      ⟨hc, le_rfl⟩ hs.2.le hpos)
  have h := canonical_analytic_on_nonpositive S F (origin + s / 1)
    (e.forward s (Ioo_subset_Icc_self hs) x) (hcanonical s hs hnot hhigh) hnonpositive
  classical
  simpa only [cylinderScalar, cylinderScalarRate, dif_pos (Ioo_subset_Icc_self hs)] using
    h.2.2.trans (mul_le_mul_of_nonneg_right hB (sq_nonneg _))

end PoincareConjecture.Proofs.M46
