import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Topology
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Uniqueness








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

namespace CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}


theorem isCompact_closure_of_scalar_proper (N : CapCertificate g)
    (D : LeviCivitaData g)
    (hproper : ∀ C : Set ℝ, IsCompact C → IsCompact (D.scalarCurvature ⁻¹' C)) :
    IsCompact (closure N.carrier) := by
  obtain ⟨p, hp⟩ := N.core_nonempty
  have hpN : p ∈ N.carrier := by
    rw [N.core_eq_interior_closed_core] at hp
    have hpclosed := interior_subset hp
    rw [N.closed_core_eq_complement_end] at hpclosed
    exact hpclosed.1
  obtain ⟨b, _, hb⟩ := N.scalar_ratio
  let C := D.scalarCurvature ⁻¹' Icc 0 (b * N.connection.scalarCurvature p)
  have hC : IsCompact C := hproper _ isCompact_Icc
  apply hC.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hC.isClosed
  intro x hx
  change 0 ≤ D.scalarCurvature x ∧ D.scalarCurvature x ≤ _
  rw [← N.connection.scalarCurvature_eq D x]
  exact ⟨(N.scalar_pos x hx).le, hb p hpN x hx⟩

end CapCertificate

namespace TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}


theorem exists_tail_disjoint_compact (e : TerminalEnd K)
    {L : Set (E.extended.slice T).carrier} (hL : IsCompact L) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → Disjoint (Subtype.val '' e.tail m) L := by
  have hK : IsClosed K.component := by
    rw [K.component_eq]
    exact isClosed_connectedComponent
  have hpre := hK.isClosedEmbedding_subtypeVal.isCompact_preimage hL
  obtain ⟨n, hn⟩ := e.exhaustion.exists_superset_of_isCompact hpre
  refine ⟨n, fun m hnm => Set.disjoint_left.mpr ?_⟩
  rintro _ ⟨x, hx, rfl⟩ hxL
  exact e.tail_subset_compl_exhaustion m hx (e.exhaustion.subset hnm (hn hxL))

theorem exists_tail_disjoint_cap (e : TerminalEnd K)
    (hproper : ∀ C : Set ℝ, IsCompact C →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' C))
    (N : CapCertificate (E.extended.metric T)) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → Disjoint (Subtype.val '' e.tail m) N.carrier := by
  obtain ⟨n, hn⟩ := e.exists_tail_disjoint_compact
    (N.isCompact_closure_of_scalar_proper (E.extended.connection T) hproper)
  exact ⟨n, fun m hnm => (hn m hnm).mono_right subset_closure⟩

end TerminalEnd

end PoincareConjecture
