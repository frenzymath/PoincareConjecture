import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.NestedComponents
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.Geometry








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.TerminalComponentPath

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} (K : TerminalComponentPath E)



theorem exists_end_meeting_of_not_isCompact {A : Set K.component}
    (hclosed : IsClosed A) (hnot : ¬ IsCompact A) :
    ∃ e : TerminalEnd K, ∀ n, (A ∩ e.tail n).Nonempty := by
  let : LocallyConnectedSpace (E.extended.slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  let : LocallyCompactSpace (E.extended.slice T).carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) _
  have hKo : IsOpen K.component := K.component_eq.symm ▸ isOpen_connectedComponent
  have hKc : IsClosed K.component := K.component_eq.symm ▸ isClosed_connectedComponent
  let : LocallyConnectedSpace K.component := hKo.locallyConnectedSpace
  let : LocallyCompactSpace K.component := hKc.locallyCompactSpace
  let : PreconnectedSpace K.component := isPreconnected_iff_preconnectedSpace.mp
    (K.component_eq.symm ▸ isPreconnected_connectedComponent)
  let C : CompactExhaustion K.component := CompactExhaustion.choice K.component
  have hA : ∀ L : Set K.component, IsCompact L → ¬ A ⊆ L := by
    intro L hL hsub
    exact hnot (hL.of_isClosed_subset hclosed hsub)
  obtain ⟨p, hp, hnest, htrace⟩ :=
    Poincare.Topology.exists_nested_unbounded_component_traces C hA
  let e : TerminalEnd K := {
    exhaustion := C
    tail := fun n => connectedComponentIn (C n)ᶜ (p n)
    tail_component := fun n => ⟨p n, hp n, rfl⟩
    nested := hnest
    escapes_compact := fun n L hL hsub => htrace n L hL (inter_subset_right.trans hsub) }
  refine ⟨e, fun n => nonempty_iff_ne_empty.mpr ?_⟩
  intro heq
  exact htrace n ∅ isCompact_empty (heq ▸ subset_rfl)



theorem isCompact_diff_of_end_tail_cover {V : Set (E.extended.slice T).carrier}
    (hV : IsOpen V)
    (hcover : ∀ e : TerminalEnd K, ∃ n, Subtype.val '' e.tail n ⊆ V) :
    IsCompact (K.component \ V) := by
  let A : Set K.component := Subtype.val ⁻¹' Vᶜ
  have hA : IsClosed A := hV.isClosed_compl.preimage continuous_subtype_val
  have hAc : IsCompact A := by
    by_contra hnot
    obtain ⟨e, he⟩ := K.exists_end_meeting_of_not_isCompact hA hnot
    obtain ⟨n, hn⟩ := hcover e
    obtain ⟨x, hxA, hx⟩ := he n
    exact hxA (hn ⟨x, hx, rfl⟩)
  have himage : Subtype.val '' A = K.component \ V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxK, hxV⟩
      exact ⟨⟨x, hxK⟩, hxV, rfl⟩
  rw [← himage]
  exact hAc.image continuous_subtype_val

end PoincareConjecture.TerminalComponentPath
