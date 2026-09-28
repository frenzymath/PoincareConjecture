import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.FiniteSubcover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.Cover

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  (Q : SingularLimitConclusion H) (rho : ℝ)

theorem exists_finite_core_cover_modulo_compact {ι : Type v}
    (V : ι → Set (Q.extension.extended.slice T).carrier)
    (hcover : ∀ K : TerminalComponentPath Q.extension,
      (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ V i) :
    ∃ (s : Finset ι) (L : Set (Q.extension.extended.slice T).carrier),
      IsCompact L ∧ SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho ⊆
        L ∪ ⋃ i ∈ s, V i := by
  classical
  obtain ⟨points, hpoints, hcore⟩ := Q.exists_finite_core_components rho
  have heach (p : points) : ∃ (s : Finset ι)
      (L : Set (Q.extension.extended.slice T).carrier),
      IsCompact L ∧ connectedComponent p.val ⊆ L ∪ ⋃ i ∈ s, V i := by
    obtain ⟨K, hK⟩ := Q.component_paths p.val
    have hcomp : K.component = connectedComponent p.val := by rw [K.component_eq, hK]
    have hlow : (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty :=
      ⟨p.val, hcomp.symm ▸ mem_connectedComponent, hpoints p.val p.property⟩
    simpa only [hcomp] using K.exists_finite_cover_modulo_compact V (hcover K hlow)
  choose s L hL hsub using heach
  refine ⟨Finset.univ.biUnion s, ⋃ p : points, L p, isCompact_iUnion hL, ?_⟩
  intro x hx
  rw [hcore] at hx
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
  rcases hsub ⟨p, hp⟩ hxp with hxL | hxV
  · exact Or.inl (mem_iUnion.mpr ⟨⟨p, hp⟩, hxL⟩)
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxV
    exact Or.inr (mem_iUnion₂.mpr ⟨i,
      Finset.mem_biUnion.mpr ⟨⟨p, hp⟩, Finset.mem_univ _, hi⟩, hxi⟩)

theorem exists_finite_isCompact_core_diff_of_end_tail_cover {ι : Type v}
    (V : ι → Set (Q.extension.extended.slice T).carrier) (hV : ∀ i, IsOpen (V i))
    (hcover : ∀ K : TerminalComponentPath Q.extension,
      (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ V i) :
    ∃ s : Finset ι, IsCompact
      (SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho \ ⋃ i ∈ s, V i) := by
  obtain ⟨s, L, hL, hsub⟩ := Q.exists_finite_core_cover_modulo_compact rho V hcover
  refine ⟨s, hL.of_isClosed_subset ?_ ?_⟩
  · exact (SurgeryTerminalCoreComponents.isClopen
      (Q.extension.extended.connection T) rho).isClosed.sdiff
        (isOpen_iUnion fun i => isOpen_iUnion fun _ => hV i)
  · intro x hx
    exact (hsub hx.1).resolve_right hx.2

theorem end_tail_cover_of_isCompact_cut_remainder {ι : Type v}
    (N : ι → EpsilonNeck (Q.extension.extended.metric T))
    (cuts : ∀ i, SurgeryEndCut (N i)) (s : Finset ι)
    (hc : IsCompact (SurgeryTerminalCoreComponents
      (Q.extension.extended.connection T) rho \ ⋃ i ∈ s, (cuts i).tail))
    (K : TerminalComponentPath Q.extension)
    (hK : (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty)
    (e : TerminalEnd K) :
    ∃ i ∈ s, ∃ n, Subtype.val '' e.tail n ⊆ (cuts i).tail := by
  have hKcore : K.component ⊆
      SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho := by
    obtain ⟨p, hpK, hp⟩ := hK
    intro x hx
    refine ⟨p, ?_, ?_⟩
    · simpa only [mem_ofPred_eq, Q.terminal_scalar_eq] using hp
    · rw [K.component_eq] at hpK hx
      rwa [← connectedComponent_eq hpK]
  let L := (SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho \
    ⋃ i ∈ s, (cuts i).tail) ∪ ⋃ i ∈ s, (N i).central_sphere
  have hL : IsCompact L := hc.union
    (s.isCompact_biUnion fun i _ => (N i).isCompact_central_sphere)
  obtain ⟨n, hn⟩ := e.exists_tail_disjoint_compact hL
  have havoid : Disjoint (Subtype.val '' e.tail n) L := hn n le_rfl
  obtain ⟨x, hx⟩ := (e.tail_connected n).nonempty
  have hximage : x.val ∈ Subtype.val '' e.tail n := ⟨x, hx, rfl⟩
  have hxunion : x.val ∈ ⋃ i ∈ s, (cuts i).tail := by
    by_contra hout
    exact disjoint_left.mp havoid hximage (Or.inl ⟨hKcore x.property, hout⟩)
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxunion
  refine ⟨i, hi, n, ?_⟩
  apply (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    ((e.tail_connected n).isPreconnected.image _ continuous_subtype_val.continuousOn)
    ?_ ⟨x.val, hximage, (cuts i).tail_isOpen.interior_eq.symm ▸ hxi⟩).trans interior_subset
  rw [(cuts i).frontier_eq]
  exact disjoint_left.mpr fun y hy hs => disjoint_left.mp havoid hy
    (Or.inr (mem_iUnion₂.mpr ⟨i, hi, hs⟩))

theorem exists_finite_end_cut_cover {ι : Type v}
    (N : ι → EpsilonNeck (Q.extension.extended.metric T))
    (cuts : ∀ i, SurgeryEndCut (N i))
    (hcover : ∀ K : TerminalComponentPath Q.extension,
      (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ (cuts i).tail) :
    ∃ s : Finset ι, IsCompact (SurgeryTerminalCoreComponents
      (Q.extension.extended.connection T) rho \ ⋃ i ∈ s, (cuts i).tail) ∧
      ∀ K : TerminalComponentPath Q.extension,
        (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
        ∀ e : TerminalEnd K, ∃ i ∈ s, ∃ n, Subtype.val '' e.tail n ⊆ (cuts i).tail := by
  obtain ⟨s, hs⟩ := Q.exists_finite_isCompact_core_diff_of_end_tail_cover rho
    (fun i => (cuts i).tail) (fun i => (cuts i).tail_isOpen) hcover
  exact ⟨s, hs, Q.end_tail_cover_of_isCompact_cut_remainder rho N cuts s hs⟩

end PoincareConjecture.SingularLimitConclusion
