import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Branch

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

theorem core_map_eq_reference_at (t : Ico H.reference.tMinus T)
    (x : (F.slice I.last_slab.start).carrier) :
    B.core_map x = B.reference_identify t
      (I.last_slab.identify
        ⟨t.1, B.reference_start_lt.le.trans t.2.1, t.2.2⟩ x) := by
  obtain ⟨t, ht⟩ := t
  rw [B.core_map_eq_reference]
  obtain heq | hlt := ht.1.eq_or_lt
  · subst t
    rfl
  have hJ : Icc H.reference.tMinus t ⊆ F.time_domain := fun s hs =>
    I.last_slab.time_subset ⟨B.reference_start_lt.le.trans hs.1, hs.2.trans_lt ht.2⟩
  have hfree : Disjoint F.surgery_times (Ioc H.reference.tMinus t) := by
    apply I.last_slab.surgery_free.mono_right
    intro s hs
    exact ⟨B.reference_start_lt.trans hs.1, hs.2.trans_lt ht.2⟩
  have hc := B.reference_transport_compatibility H.reference.tMinus t hlt hJ hfree
    H.reference.tMinus t ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩
    ⟨le_rfl, H.reference.tMinus_lt⟩ ht
    (I.last_slab.identify
      ⟨H.reference.tMinus, B.reference_start_lt.le, H.reference.tMinus_lt⟩ x)
  have hc' := I.last_slab.transport_compatibility H.reference.tMinus t hlt hJ hfree
    H.reference.tMinus t ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩
    ⟨B.reference_start_lt.le, H.reference.tMinus_lt⟩
    ⟨B.reference_start_lt.le.trans ht.1, ht.2⟩ x
  rw [hc'] at hc
  exact hc.symm

theorem reference_scalar_core_map (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T)
    (x : (F.slice I.last_slab.start).carrier) :
    H.reference.scalar t (B.core_map x) =
      (I.last_slab.flow.connection t).scalarCurvature x := by
  rw [B.core_map_eq_reference_at ⟨t, ht⟩]
  exact B.reference_scalar_pullback ⟨t, ht⟩ x

end PoincareConjecture.RepairedContinuationLimitBridge
