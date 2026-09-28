import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.InitialSlabTransport
import PoincareConjecture.Proofs.M45.Sec15_2_Constants.ProducerEndpoints
import PoincareConjecture.Proofs.M45.InitialGeometry
import PoincareConjecture.Proofs.M33.RegularHistory










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M45



theorem initial_curvature_on_free_interval (F : SurgeryFlowData.{u})
    (hunique : RicciFlowUniqueness 3 (F.slice 0).carrier)
    (G : RicciFlow 3 (F.slice 0).carrier (Icc 0 (1 / 16 : ℝ)))
    (hG : G.metric 0 = F.metric 0)
    (hRm : ∀ t ∈ Icc 0 (1 / 16 : ℝ), ∀ x : (F.slice 0).carrier,
      (G.connection t).curvatureTensorNorm x ≤ 2)
    {t : ℝ} (ht : 0 < t) (htF : t ∈ F.time_domain) (htB : t ≤ 1 / 16)
    (hfree : Disjoint F.surgery_times (Ioc 0 t)) (x : (F.slice t).carrier) :
    (F.connection t).curvatureTensorNorm x ≤ 2 := by
  let S := F.regular_slabs 0 t ht
    (F.time_domain_interval.out F.zero_mem htF) hfree
  let tt : Icc 0 t := ⟨t, ht.le, le_rfl⟩
  have heq := initialSlab_curvature_eq F hunique G hG htB S tt ((S.identify tt).symm x)
  have hbound := hRm t ⟨ht.le, htB⟩ ((S.identify tt).symm x)
  simpa only [Diffeomorph.apply_symm_apply] using heq.trans_le hbound



theorem no_initial_surgery_of_regular_curvature (F : SurgeryFlowData.{u})
    (hbound : ∀ t : ℝ, 0 < t → t ∈ F.time_domain → t ≤ 1 / 16 →
      Disjoint F.surgery_times (Ioc 0 t) →
        ∀ x : (F.slice t).carrier, (F.connection t).curvatureTensorNorm x ≤ 2) :
    Disjoint F.surgery_times (Icc 0 (1 / 16 : ℝ)) := by
  classical
  let : Nonempty (F.slice 0).carrier := F.initial_nonempty
  apply Set.disjoint_left.mpr
  intro T hT htB
  have hprefix : Icc 0 T ⊆ F.time_domain :=
    F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
  have hfinite := F.surgery_times_finite_on_compact isCompact_Icc hprefix
  obtain ⟨b, hb, hminimal⟩ := Set.exists_min_image
    (F.surgery_times ∩ Icc 0 T) (fun s : ℝ => s) hfinite
    ⟨T, hT, htB.1, le_rfl⟩
  have hbpos : 0 < b := lt_of_le_of_ne hb.2.1 (by
    intro h
    exact F.zero_not_surgery (h ▸ hb.1))
  have hbF : b ∈ F.time_domain := F.surgery_times_subset hb.1
  have hJ : Icc 0 b ⊆ F.time_domain := F.time_domain_interval.out F.zero_mem hbF
  have hfree : Disjoint F.surgery_times (Ioo 0 b) := by
    apply Set.disjoint_left.mpr
    intro s hs hsb
    exact (not_lt_of_ge (hminimal s ⟨hs, hsb.1.le, hsb.2.le.trans hb.2.2⟩)) hsb.2
  obtain ⟨t, ht, x, hx⟩ := F.maximal_intervals 0 b F.zero_mem (Or.inl rfl)
    hbpos (Ico_subset_Icc_self.trans hJ) hfree (Or.inl hb.1) 2 0 hbpos
  have htpos : 0 < t := by simpa only [max_self] using ht.1
  have htF : t ∈ F.time_domain := hJ ⟨htpos.le, ht.2.le⟩
  have htB' : t ≤ 1 / 16 := ht.2.le.trans (hb.2.2.trans htB.2)
  have hfree' : Disjoint F.surgery_times (Ioc 0 t) := by
    apply Set.disjoint_left.mpr
    intro s hs hst
    exact Set.disjoint_left.mp hfree hs ⟨hst.1, hst.2.trans_lt ht.2⟩
  exact (not_lt_of_ge (hbound t htpos htF htB' hfree' x)) hx




theorem initialCaptureProducer
    (h03 : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [SecondCountableTopology M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [CompactSpace M], RicciFlowLocalTheory 3 M) :
    InitialCaptureProducer.{u} := by
  intro epsilon kappa _hepsilon _hle _hkappa seed F
  let : CompactSpace (F.slice 0).carrier :=
    isCompact_univ_iff.mp (F.slices_compact 0 F.zero_mem)
  obtain ⟨G, hG, _hD, hRm, hvolume⟩ := seed F.normalizedInitialData
  change G.metric 0 = F.metric 0 at hG
  have hunique := (h03 (F.slice 0).carrier).2.1
  have hbound (t : ℝ) := initial_curvature_on_free_interval F hunique G hG hRm (t := t)
  have hfree := no_initial_surgery_of_regular_curvature F
    (fun t ht htF htB hfree x => hbound t ht htF htB hfree x)
  refine ⟨hfree, ?_⟩
  intro t htF htB x
  have ht0 : 0 ≤ t := F.time_domain_nonnegative htF
  have hfree' : Disjoint F.surgery_times (Ioc 0 t) :=
    hfree.mono_right (show Ioc 0 t ⊆ Icc 0 (1 / 16 : ℝ) from
      fun _ hs => ⟨hs.1.le, hs.2.trans htB⟩)
  have hcurv : (F.connection t).curvatureTensorNorm x ≤ 2 := by
    by_cases htzero : t = 0
    · subst t
      exact (F.initial_normalized x).1.trans (by norm_num)
    · exact hbound t (lt_of_le_of_ne ht0 (Ne.symm htzero)) htF htB hfree' x
  refine ⟨hcurv, scalar_le_eighteen_of_curvature_le_two (F.connection t) x hcurv, ?_⟩
  intro r hr hrepsilon
  by_cases htzero : t = 0
  · subst t
    have h := hvolume 0 (by norm_num) x r hr hrepsilon
    simpa only [hG] using h
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
    let S := F.regular_slabs 0 t htpos
      (F.time_domain_interval.out F.zero_mem htF) hfree'
    let tt : Icc 0 t := ⟨t, ht0, le_rfl⟩
    have htransport := initialSlab_ball_volume_eq F hunique G hG htB S tt
      ((S.identify tt).symm x) r
    have h := hvolume t ⟨ht0, htB⟩ ((S.identify tt).symm x) r hr hrepsilon
    simpa only [Diffeomorph.apply_symm_apply] using h.trans_eq htransport.symm

end PoincareConjecture.M45
