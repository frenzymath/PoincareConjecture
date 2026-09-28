import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Components
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BallPreimage
import Mathlib.Topology.Connected.Clopen

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TerminalEnd

variable {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension G T} {K : TerminalComponentPath E} (e : TerminalEnd K)

theorem isConnected_tail (n : ℕ) : IsConnected (e.tail n) := by
  obtain ⟨x, hx, heq⟩ := e.tail_component n
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr hx

include e in

theorem not_isCompact_component : ¬ IsCompact K.component := by
  intro hK
  let : CompactSpace K.component := isCompact_iff_compactSpace.mp hK
  exact e.escapes_compact 0 univ isCompact_univ (subset_univ _)

end PoincareConjecture.TerminalEnd

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem exists_end_tail_scalar_gt (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K) (q : ℝ) :
    ∃ n, ∀ x ∈ e.tail n, q < Q.terminal_scalar x.val := by
  have hK : IsClosed K.component := K.component_eq ▸ isClosed_connectedComponent
  have hcompact : IsCompact {x : K.component | Q.terminal_scalar x.val ≤ q} := by
    change IsCompact (Subtype.val ⁻¹' {x | Q.terminal_scalar x ≤ q})
    apply hK.isClosedEmbedding_subtypeVal.isCompact_preimage
    simpa only [Q.terminal_scalar_eq] using Q.isCompact_scalar_sublevel q
  obtain ⟨n, hn⟩ := e.exhaustion.exists_superset_of_isCompact hcompact
  obtain ⟨z, hz, htail⟩ := e.tail_component n
  refine ⟨n, fun x hx => lt_of_not_ge fun hle => ?_⟩
  have hout : x ∈ (e.exhaustion n)ᶜ := by
    rw [htail] at hx
    exact connectedComponentIn_subset _ _ hx
  exact hout (hn hle)

theorem exists_end_superlevel_region (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K) (q : ℝ)
    (hlow : ∃ x ∈ K.component, Q.terminal_scalar x < q) :
    ∃ (n : ℕ) (X : Set (Q.extension.extended.slice T).carrier),
      IsClosed X ∧ IsConnected X ∧ X ⊆ K.component ∧
      Subtype.val '' e.tail n ⊆ X ∧ ¬ IsCompact X ∧
      (∀ x ∈ X, q ≤ Q.terminal_scalar x) ∧
      ∃ x ∈ X, Q.terminal_scalar x = q := by
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
  obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨hD.nonempty, hDproper⟩
  have hzq : f z = q := by
    have hfront := hf.frontier_preimage_subset (Ioi q)
      (Poincare.Topology.frontier_connectedComponentIn_subset_of_isOpen hO p hz)
    simpa only [frontier_Ioi, mem_preimage, mem_singleton_iff] using hfront
  let X : Set (Q.extension.extended.slice T).carrier := Subtype.val '' closure D
  have hbound : closure D ⊆ {x | q ≤ f x} :=
    closure_minimal (fun x hx => le_of_lt (show q < f x from connectedComponentIn_subset O p hx))
      (isClosed_le continuous_const hf)
  refine ⟨n, X, hKclosed.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closure,
    hD.closure.image _ continuous_subtype_val.continuousOn,
    ?_, image_mono (htailD.trans subset_closure), ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact y.property
  · intro hX
    exact e.escapes_compact n (Subtype.val ⁻¹' X)
      (hKclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hX)
      (fun x hx => ⟨x, subset_closure (htailD hx), rfl⟩)
  · rintro x ⟨y, hy, rfl⟩
    exact hbound hy
  · exact ⟨z.val, ⟨z, hz.1, rfl⟩, hzq⟩

end PoincareConjecture.SingularLimitConclusion
