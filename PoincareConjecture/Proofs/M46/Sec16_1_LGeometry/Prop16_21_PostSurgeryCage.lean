import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_21_CapOrdinaryCoordinates
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_21_CompactRetainedSlice
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

theorem exists_compact_postSurgery_cage
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) (G : FlowBoxRicciGeometry H.generalized)
    {t T A c mu theta : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (htT : t < T)
    (hwindow : Icc 0 T ⊆ H.generalized.interval)
    (hA : F.standard_initial.cylindrical_end.radius + 5 < A / 2)
    (Q : ∀ i : Fin (F.event t hT).cap_count,
      CapBarrierWindow G (F.slice t) (F.metric t) ((F.event t hT).caps i).tip
        t T A (F.parameters.h t) c mu theta)
    (D : ∀ i, CapBarrierOriginData H (Q i))
    {Z : Set H.generalized.point}
    (havoid : ∀ v ∈ Z, ∀ i, v ∉ (Q i).earlyInnerTrace)
    (hbirth : ∀ y : (H.generalized.slice t).carrier,
      (⟨t, y⟩ : H.generalized.point) ∈ Z →
        H.history.forward t
          (hwindow ⟨F.time_domain_nonnegative (F.surgery_times_subset hT), htT.le⟩) y ∈
            surgeryCapExcludedSlice F t hT (A / 2)) :
    ∃ N : Set H.generalized.point, IsCompact N ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ v ∈ Z, v.1 ∈ Icc t (t + delta) → v ∈ N := by
  have ht0 : 0 ≤ t := F.time_domain_nonnegative (F.surgery_times_subset hT)
  have hh : 0 < F.parameters.h t := F.parameters.h_pos t ht0
  have hsq : 0 < (F.parameters.h t) ^ 2 := sq_pos_of_pos hh
  have hApos : 0 < A := by linarith [F.standard_initial.cylindrical_end.radius_pos]
  obtain ⟨b, htb, hbT, hNo⟩ :=
    M44.exists_surgery_free_right_interval F (F.surgery_times_subset hT) htT
  have hJ : Icc t b ⊆ F.time_domain := by
    intro s hs
    exact W.time_subset (H.interval_eq ▸ hwindow ⟨ht0.trans hs.1, hs.2.trans hbT.le⟩)
  have hwin : Icc t b ⊆ H.generalized.interval :=
    fun _ hs => hwindow ⟨ht0.trans hs.1, hs.2.trans hbT.le⟩
  obtain ⟨hK, hregular⟩ := surgeryCapExcludedSlice_compact_regular F t hT hA
  obtain ⟨N, hN, htrace⟩ := exists_compact_ordinary_history_trace H htb hJ hNo hwin
    hK hregular
  have hnear : {s : ℝ | ∀ i, s < (Q i).top} ∈ 𝓝 t :=
    eventually_all.mpr (fun i => Iio_mem_nhds (Q i).top_gt)
  obtain ⟨epsilon, hepsilon, hcap⟩ := Metric.mem_nhds_iff.mp hnear
  let delta := min ((b - t) / 2) (min (epsilon / 2) ((F.parameters.h t) ^ 2 / 4))
  have hd : 0 < delta :=
    lt_min (half_pos (sub_pos.mpr htb)) (lt_min (half_pos hepsilon) (by positivity))
  have hdb : delta < b - t := (min_le_left _ _).trans_lt (half_lt_self (sub_pos.mpr htb))
  have hde : delta < epsilon :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hepsilon)
  have hdscale : delta ≤ (F.parameters.h t) ^ 2 / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hcaps : ∀ i, t + delta < (Q i).top := by
    apply hcap
    simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hd] using hde
  refine ⟨N, hN, delta, hd, ?_⟩
  rintro ⟨u, y⟩ hz hu
  change u ∈ Icc t (t + delta) at hu
  have hub : u ∈ Icc t b := ⟨hu.1, by linarith [hu.2]⟩
  apply htrace u hub y
  let S := F.regular_slabs t b htb hJ hNo
  rcases hu.1.eq_or_lt with htu | htu
  · subst u
    have hinv : (S.identify ⟨t, hub⟩).symm (H.history.forward t (hwin hub) y) =
        H.history.forward t (hwin hub) y := by
      exact (S.initial_identify ((S.identify ⟨t, hub⟩).symm
        (H.history.forward t (hwin hub) y))).symm.trans
          ((S.identify ⟨t, hub⟩).apply_symm_apply _)
    rw [hinv]
    exact hbirth y hz
  · generalize hs : (u - t) / (F.parameters.h t) ^ 2 = s
    have hs0 : 0 < s := hs ▸ div_pos (sub_pos.mpr htu) hsq
    have hsearly : s ≤ 1 / 2 := by
      rw [← hs, div_le_iff₀ hsq]
      linarith [hu.2]
    have hclock : t + s / ((F.parameters.h t)⁻¹ ^ 2) = u := by
      rw [← hs, inv_pow, div_inv_eq_mul, div_mul_cancel₀ _ hsq.ne']
      ring
    have hinterval (i : Fin (F.event t hT).cap_count) : s ∈ (Q i).interval.domain := by
      rw [(D i).interval_eq]
      refine ⟨hs0, ?_⟩
      rw [← hs, div_lt_div_iff_of_pos_right hsq]
      linarith [hcaps i, hu.2]
    have hinner (i : Fin (F.event t hT).cap_count) :
        (S.identify ⟨u, hub⟩).symm (H.history.forward u (hwin hub) y) ∉
          (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t / 2) := by
      cases hclock
      exact (D i).ordinary_coordinate_not_inner H (Q i) hApos hh htb hJ hNo
        (hinterval i) hsearly hub y (havoid _ hz i)
    intro hbad
    obtain ⟨i, hi⟩ := mem_iUnion.mp hbad
    apply hinner i
    have hradius : (A / 2) * F.parameters.h t = A * F.parameters.h t / 2 := by ring
    simpa only [hradius] using hi

end PoincareConjecture.Proofs.M46
