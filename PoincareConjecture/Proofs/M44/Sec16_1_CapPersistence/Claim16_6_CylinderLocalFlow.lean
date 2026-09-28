import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderSlabSmooth
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderEventSmooth
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_PreterminalStopping

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale B : ℝ} {U : Set C.carrier}

theorem cylinderTimeCoefficients_local_smooth_ricci
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 B) U) (hU : IsOpen U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) (hmap : f.target ⊆ U)
    (r0 : ℝ) (hr0 : r0 ∈ Ico 0 B) (s : ℝ) (hs : s ∈ Ico 0 B) :
    ∃ K : Set ℝ, K ∈ 𝓝 (origin + s / scale) ∧ origin + s / scale ∈ K ∧
      ContDiffOn ℝ ∞ (cylinderTimeCoefficients e f r0 hr0)
        ((Ico origin (origin + B / scale) ∩ K) ×ˢ f.source) ∧
      ∀ t ∈ Ico origin (origin + B / scale) ∩ K, ∀ y ∈ f.source,
        HasDerivWithinAt (fun r => cylinderTimeCoefficients e f r0 hr0 (r, y))
          (SpacetimeBounds.ricciFlowOperator 3 (SpacetimeBounds.metricTwoJet
            (fun z => cylinderTimeCoefficients e f r0 hr0 (t, z)) y))
          (Ico origin (origin + B / scale) ∩ K) t := by
  let J := Ico origin (origin + B / scale)
  have hJI (t : ℝ) (ht : t ∈ J) : scale * (t - origin) ∈ Ico 0 B :=
    (cylinder_parameter_mem_ico e B t).mpr ht
  have hdomain (t : ℝ) (ht : t ∈ J) : t ∈ F.time_domain :=
    cylinder_parameter_time_mem e (hJI t ht)
  have htime : origin + s / scale ∈ F.time_domain :=
    e.time_subset (mem_image_of_mem _ hs)
  have hend : origin + s / scale < origin + B / scale := by
    linarith [(div_lt_div_iff_of_pos_right e.scale_pos).mpr hs.2]
  by_cases hzero : s = 0
  · subst s
    simp only [zero_div, add_zero] at htime hend ⊢
    obtain ⟨b, h0b, hbend, hNo⟩ := exists_surgery_free_right_interval F htime hend
    have hslab : Icc origin b ⊆ F.time_domain :=
      fun t ht => hdomain t ⟨ht.1, ht.2.trans_lt hbend⟩
    have hr' : origin + 0 / scale ∈ Icc origin b := by simp [h0b.le]
    have hresult := cylinderTimeCoefficients_slab_smooth_ricci e hU f hmap r0 hr0
      h0b hslab hNo 0 hs hr'
      (J := J ∩ Iio b) (fun t ht => hJI t ht.1)
      (fun _ ht => ⟨ht.1.1, ht.2.le⟩)
    exact ⟨Iio b, Iio_mem_nhds h0b, h0b, hresult⟩
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hzero)
    have hstart : origin < origin + s / scale := by linarith [div_pos hspos e.scale_pos]
    by_cases hT : origin + s / scale ∈ F.surgery_times
    · let : Nonempty (F.slice (origin + s / scale)).carrier := ⟨e.forward s hs (f 0)⟩
      let event := F.event (origin + s / scale) hT
      have hfree := event_preterminal_surgery_free P F hpinch hT
      obtain ⟨r, hr, hr'⟩ := exists_preterminal_parameter e.scale_pos hspos event.tMinus_lt
      have hrI : r ∈ Ico 0 B := ⟨hr.1, hr.2.trans hs.2⟩
      obtain ⟨b, hTb, hbend, hNo⟩ := exists_surgery_free_right_interval F htime hend
      have hslab : Icc (origin + s / scale) b ⊆ F.time_domain :=
        fun t ht => hdomain t ⟨hstart.le.trans ht.1, ht.2.trans_lt hbend⟩
      let K := Ioo (max origin event.tMinus) b
      have hK : K ∈ 𝓝 (origin + s / scale) :=
        Ioo_mem_nhds (max_lt hstart event.tMinus_lt) hTb
      have hsK : origin + s / scale ∈ K := ⟨max_lt hstart event.tMinus_lt, hTb⟩
      have hresult := cylinderTimeCoefficients_event_smooth_ricci e hU f hmap r0 hr0
        s hs hT hfree r hrI hr' hTb hslab hNo
        (J := J ∩ K) (fun t ht => hJI t ht.1)
        (fun _ ht => ⟨(le_max_right _ _).trans_lt ht.2.1, ht.2.2⟩)
      exact ⟨K, hK, hsK, hresult⟩
    · obtain ⟨a, b, hoa, hat, htb, hbe, hfree⟩ :=
        exists_surgery_free_closed_neighborhood F htime hstart hend hT
      have hslab : Icc a b ⊆ F.time_domain :=
        fun t ht => hdomain t ⟨hoa.le.trans ht.1, ht.2.trans_lt hbe⟩
      have hNo := hfree.mono_right Ioc_subset_Icc_self
      have hr' : origin + s / scale ∈ Icc a b := ⟨hat.le, htb.le⟩
      have hresult := cylinderTimeCoefficients_slab_smooth_ricci e hU f hmap r0 hr0
        (hat.trans htb) hslab hNo s hs hr'
        (J := J ∩ Ioo a b) (fun t ht => hJI t ht.1)
        (fun _ ht => ⟨ht.2.1.le, ht.2.2.le⟩)
      exact ⟨Ioo a b, Ioo_mem_nhds hat htb, ⟨hat, htb⟩, hresult⟩

end PoincareConjecture.M44
