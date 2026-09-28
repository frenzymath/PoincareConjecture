import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.ScalarEscape
import Mathlib.Topology.Connected.LocallyConnected









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}

theorem tail_connected (e : TerminalEnd K) (n : ℕ) : IsConnected (e.tail n) := by
  obtain ⟨x, hx, heq⟩ := e.tail_component n
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr hx

theorem tail_image_connected (e : TerminalEnd K) (n : ℕ) :
    IsConnected (Subtype.val '' e.tail n : Set (E.extended.slice T).carrier) :=
  (e.tail_connected n).image _ continuous_subtype_val.continuousOn

theorem tail_image_open (e : TerminalEnd K) (n : ℕ) :
    IsOpen (Subtype.val '' e.tail n : Set (E.extended.slice T).carrier) := by
  let _ : LocallyConnectedSpace (E.extended.slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  have hK : IsOpen K.component := by
    rw [K.component_eq]
    exact isOpen_connectedComponent
  let _ : LocallyConnectedSpace K.component := hK.locallyConnectedSpace
  obtain ⟨x, _, heq⟩ := e.tail_component n
  apply hK.isOpenMap_subtype_val
  rw [heq]
  exact (e.exhaustion.isCompact n).isClosed.isOpen_compl.connectedComponentIn

theorem tail_image_not_subset_compact (e : TerminalEnd K) (n : ℕ)
    {L : Set (E.extended.slice T).carrier} (hL : IsCompact L) :
    ¬ Subtype.val '' e.tail n ⊆ L := by
  have hK : IsClosed K.component := by
    rw [K.component_eq]
    exact isClosed_connectedComponent
  intro hsub
  exact e.escapes_compact n (Subtype.val ⁻¹' L)
    (hK.isClosedEmbedding_subtypeVal.isCompact_preimage hL)
    (fun x hx => hsub ⟨x, hx, rfl⟩)

theorem component_not_compact (e : TerminalEnd K) : ¬ IsCompact K.component := by
  intro hK
  exact e.tail_image_not_subset_compact 0 hK (by rintro _ ⟨x, _, rfl⟩; exact x.property)

theorem not_mem_compact_component (e : TerminalEnd K)
    {x y : (E.extended.slice T).carrier} (hx : x ∈ K.component)
    (hy : x ∈ connectedComponent y) : ¬ IsCompact (connectedComponent y) := by
  have hxy : connectedComponent y = K.component := by
    rw [K.component_eq] at hx ⊢
    exact (connectedComponent_eq hy).trans (connectedComponent_eq hx).symm
  simpa only [hxy] using e.component_not_compact


theorem not_mem_cComponent (e : TerminalEnd K) {C : ℝ}
    (N : SingularCComponent (E.extended.metric T) (E.extended.connection T) C)
    {x : (E.extended.slice T).carrier} (hx : x ∈ K.component) : x ∉ N.carrier := by
  intro hxN
  exact e.not_mem_compact_component hx (N.component_eq ▸ hxN)
    (N.component_eq ▸ N.compact)


theorem not_mem_roundComponent (e : TerminalEnd K) {epsilon : ℝ}
    (N : SingularRoundComponent (E.extended.metric T) epsilon)
    {x : (E.extended.slice T).carrier} (hx : x ∈ K.component) : x ∉ N.carrier := by
  intro hxN
  exact e.not_mem_compact_component hx (N.component_eq ▸ hxN)
    (N.component_eq ▸ N.compact)

end PoincareConjecture.TerminalEnd
