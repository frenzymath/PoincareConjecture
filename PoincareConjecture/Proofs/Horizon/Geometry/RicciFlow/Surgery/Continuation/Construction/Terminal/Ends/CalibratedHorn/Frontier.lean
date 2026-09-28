import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Superlevel

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem exists_end_superlevel_region_compact_frontier
    (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K) (q : ℝ)
    (hlow : ∃ x ∈ K.component, Q.terminal_scalar x < q) :
    ∃ (n : ℕ) (X : Set (Q.extension.extended.slice T).carrier),
      IsClosed X ∧ IsConnected X ∧ X ⊆ K.component ∧
      Subtype.val '' e.tail n ⊆ X ∧ ¬ IsCompact X ∧
      (∀ x ∈ X, q ≤ Q.terminal_scalar x) ∧
      (∃ x ∈ X, Q.terminal_scalar x = q) ∧
      IsCompact (frontier X) ∧
      ∀ x ∈ frontier X, Q.terminal_scalar x = q := by
  let : LocallyConnectedSpace (Q.extension.extended.slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  have hKclosed : IsClosed K.component := K.component_eq ▸ isClosed_connectedComponent
  have hKopen : IsOpen K.component := K.component_eq ▸ isOpen_connectedComponent
  have hKconn : IsConnected K.component := K.component_eq ▸ isConnected_connectedComponent
  let : LocallyConnectedSpace K.component := hKopen.locallyConnectedSpace
  let : PreconnectedSpace K.component := Subtype.preconnectedSpace hKconn.isPreconnected
  let f : K.component → ℝ := fun x => Q.terminal_scalar x.val
  have hf : Continuous f := by
    dsimp only [f]
    rw [Q.terminal_scalar_eq]
    exact (Q.extension.extended.connection T).continuous_scalarCurvature.comp continuous_subtype_val
  obtain ⟨n, hn⟩ := Q.exists_end_tail_scalar_gt K e q
  obtain ⟨p, hp⟩ := (e.isConnected_tail n).nonempty
  let O : Set K.component := f ⁻¹' Ioi q
  let D := connectedComponentIn O p
  have hO : IsOpen O := isOpen_Ioi.preimage hf
  have hpO : p ∈ O := hn p hp
  have hD : IsConnected D := isConnected_connectedComponentIn_iff.mpr hpO
  have htailD : e.tail n ⊆ D := (e.isConnected_tail n).isPreconnected.subset_connectedComponentIn
    hp (fun x hx => hn x hx)
  have hDproper : D ≠ univ := by
    obtain ⟨x, hxK, hxq⟩ := hlow
    intro heq
    have hxD : (⟨x, hxK⟩ : K.component) ∈ D := heq ▸ mem_univ _
    exact (not_lt_of_ge hxq.le) (connectedComponentIn_subset O p hxD)
  have hfrontD : ∀ z ∈ frontier D, f z = q := by
    intro z hz
    have hfront := hf.frontier_preimage_subset (Ioi q)
      (Poincare.Topology.frontier_connectedComponentIn_subset_of_isOpen hO p hz)
    simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hfront
  obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨hD.nonempty, hDproper⟩
  let X : Set (Q.extension.extended.slice T).carrier := Subtype.val '' closure D
  have hclosed : IsClosed X :=
    hKclosed.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closure
  have hsub : X ⊆ K.component := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hbound : closure D ⊆ {x | q ≤ f x} :=
    closure_minimal (fun x hx => le_of_lt (show q < f x from connectedComponentIn_subset O p hx))
      (isClosed_le continuous_const hf)
  have hpre : (Subtype.val ⁻¹' X : Set K.component) = closure D :=
    Subtype.coe_injective.preimage_image _
  have hfrontpre : (Subtype.val ⁻¹' frontier X : Set K.component) = frontier (closure D) := by
    rw [hKopen.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val, hpre]
  have hfrontX : ∀ x ∈ frontier X, Q.terminal_scalar x = q := by
    intro x hx
    have hxK := hsub (hclosed.frontier_subset hx)
    have hxD : (⟨x, hxK⟩ : K.component) ∈ frontier (closure D) := by
      rw [← hfrontpre]
      exact hx
    exact hfrontD ⟨x, hxK⟩ (frontier_closure_subset hxD)
  refine ⟨n, X, hclosed, hD.closure.image _ continuous_subtype_val.continuousOn,
    hsub, image_mono (htailD.trans subset_closure), ?_, ?_,
    ⟨z.val, ⟨z, hz.1, rfl⟩, hfrontD z hz⟩, ?_, hfrontX⟩
  · intro hX
    exact e.escapes_compact n (Subtype.val ⁻¹' X)
      (hKclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hX)
      (fun x hx => ⟨x, subset_closure (htailD hx), rfl⟩)
  · rintro x ⟨y, hy, rfl⟩
    exact hbound hy
  · exact (Q.scalar_proper {q} isCompact_singleton).of_isClosed_subset isClosed_frontier
      (fun x hx => hfrontX x hx)

end PoincareConjecture.SingularLimitConclusion
