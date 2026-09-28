import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.FiniteSubcoverTraces
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.TerminalEnd








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.TerminalComponentPath

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} (K : TerminalComponentPath E)

theorem exists_finite_cover_modulo_compact {ι : Type v}
    (V : ι → Set (E.extended.slice T).carrier)
    (hcover : ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ V i) :
    ∃ (s : Finset ι) (L : Set (E.extended.slice T).carrier),
      IsCompact L ∧ K.component ⊆ L ∪ ⋃ i ∈ s, V i := by
  classical
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
  let W : ι → Set K.component := fun i => Subtype.val ⁻¹' V i
  have hfinite : ∃ (s : Finset ι) (L : Set K.component),
      IsCompact L ∧ univ ⊆ L ∪ ⋃ i ∈ s, W i := by
    by_contra h
    push Not at h
    obtain ⟨p, hp, hnest, htrace⟩ :=
      Poincare.Topology.exists_nested_component_traces_without_finite_cover C W h
    let e : TerminalEnd K := {
      exhaustion := C
      tail := fun n => connectedComponentIn (C n)ᶜ (p n)
      tail_component := fun n => ⟨p n, hp n, rfl⟩
      nested := hnest
      escapes_compact := by
        intro n L hL hsub
        apply htrace n ∅ L hL
        simpa only [univ_inter, Finset.notMem_empty, iUnion_of_empty,
          iUnion_empty, union_empty] using hsub }
    obtain ⟨i, n, hn⟩ := hcover e
    apply htrace n {i} ∅ isCompact_empty
    intro x hx
    exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_singleton_self _, hn ⟨x, hx.2, rfl⟩⟩)
  obtain ⟨s, L, hL, hsub⟩ := hfinite
  refine ⟨s, Subtype.val '' L, hL.image continuous_subtype_val, ?_⟩
  intro x hx
  rcases hsub (mem_univ (⟨x, hx⟩ : K.component)) with hxL | hxV
  · exact Or.inl ⟨⟨x, hx⟩, hxL, rfl⟩
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxV
    exact Or.inr (mem_iUnion₂.mpr ⟨i, hi, hxi⟩)


theorem exists_finite_isCompact_diff_of_end_tail_cover {ι : Type v}
    (V : ι → Set (E.extended.slice T).carrier) (hV : ∀ i, IsOpen (V i))
    (hcover : ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ V i) :
    ∃ s : Finset ι, IsCompact (K.component \ ⋃ i ∈ s, V i) := by
  obtain ⟨s, L, hL, hsub⟩ := K.exists_finite_cover_modulo_compact V hcover
  refine ⟨s, hL.of_isClosed_subset ?_ ?_⟩
  · exact (K.component_eq.symm ▸ isClosed_connectedComponent).sdiff
      (isOpen_iUnion fun i => isOpen_iUnion fun _ => hV i)
  · intro x hx
    exact (hsub hx.1).resolve_right hx.2

end PoincareConjecture.TerminalComponentPath
