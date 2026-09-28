import PoincareConjecture.Definitions.M33BranchContinuation









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture


theorem RepairedPreterminalSlab.exists_regular_reference
    {F : SurgeryFlowData.{u}} {T : ℝ} (P : RepairedPreterminalSlab F T)
    (b : ℝ) (hb : b < T) :
    ∃ t : ℝ, max P.start b < t ∧ t < T ∧
      t ∈ F.time_domain ∧ t ∉ F.surgery_times := by
  obtain ⟨t, ht, hT⟩ := exists_between (max_lt P.start_lt hb)
  have hstart : P.start < t := (le_max_left _ _).trans_lt ht
  refine ⟨t, ht, hT, P.time_subset ⟨hstart.le, hT⟩, ?_⟩
  exact fun hS => Set.disjoint_left.mp P.surgery_free hS ⟨hstart, hT⟩

namespace RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B in

theorem reference_window_subset :
    Set.Ico H.reference.tMinus T ⊆ Set.Ico I.last_slab.start T :=
  fun _ ht => ⟨B.reference_start_lt.le.trans ht.1, ht.2⟩

noncomputable def referenceCoreEquiv :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice I.last_slab.start).carrier M ∞ :=
  (I.last_slab.identify
    ⟨H.reference.tMinus, B.reference_start_lt.le, H.reference.tMinus_lt⟩).trans
    (B.reference_identify ⟨H.reference.tMinus, le_rfl, H.reference.tMinus_lt⟩)

theorem referenceCoreEquiv_apply (x : (F.slice I.last_slab.start).carrier) :
    B.referenceCoreEquiv x = B.core_map x :=
  (B.core_map_eq_reference x).symm

theorem core_map_bijective : Function.Bijective B.core_map := by
  have h : B.core_map = B.referenceCoreEquiv :=
    funext (fun x => (B.referenceCoreEquiv_apply x).symm)
  rw [h]
  exact B.referenceCoreEquiv.bijective


theorem reference_identify_last_slab (t : Set.Ico H.reference.tMinus T)
    (x : (F.slice I.last_slab.start).carrier) :
    B.reference_identify t (I.last_slab.identify ⟨t.1, B.reference_window_subset t.2⟩ x) =
      B.core_map x := by
  obtain ⟨v, htv, hvT⟩ := exists_between t.2.2
  have huv : H.reference.tMinus < v := t.2.1.trans_lt htv
  have hJ : Set.Icc H.reference.tMinus v ⊆ F.time_domain := by
    intro s hs
    exact I.last_slab.time_subset
      ⟨B.reference_start_lt.le.trans hs.1, hs.2.trans_lt hvT⟩
  have hSubset : Set.Ioc H.reference.tMinus v ⊆ Set.Ioo I.last_slab.start T := by
    intro s hs
    exact ⟨B.reference_start_lt.trans hs.1, hs.2.trans_lt hvT⟩
  have hS : Disjoint F.surgery_times (Set.Ioc H.reference.tMinus v) :=
    I.last_slab.surgery_free.mono_right hSubset
  have hRaw := I.last_slab.transport_compatibility
    H.reference.tMinus v huv hJ hS H.reference.tMinus t.1
    ⟨le_rfl, huv.le⟩ ⟨t.2.1, htv.le⟩
    ⟨B.reference_start_lt.le, H.reference.tMinus_lt⟩
    (B.reference_window_subset t.2) x
  have hRef := B.reference_transport_compatibility
    H.reference.tMinus v huv hJ hS H.reference.tMinus t.1
    ⟨le_rfl, huv.le⟩ ⟨t.2.1, htv.le⟩
    ⟨le_rfl, H.reference.tMinus_lt⟩ t.2
    (I.last_slab.identify
      ⟨H.reference.tMinus, B.reference_start_lt.le, H.reference.tMinus_lt⟩ x)
  rw [hRaw] at hRef
  exact hRef.trans (B.core_map_eq_reference x).symm

end RepairedContinuationLimitBridge

end PoincareConjecture
