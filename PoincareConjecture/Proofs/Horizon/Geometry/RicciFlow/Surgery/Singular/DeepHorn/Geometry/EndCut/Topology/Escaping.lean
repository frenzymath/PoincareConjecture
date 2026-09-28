import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.EndCut.Component








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

noncomputable def escapingPoint (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    (E.extended.slice T).carrier :=
  Classical.choose (horn.exists_unique_escaping_component K hK)

noncomputable def escapingComponent (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    Set (E.extended.slice T).carrier :=
  connectedComponentIn (horn.carrier \ K) (horn.escapingPoint K hK)

theorem escapingPoint_mem (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    horn.escapingPoint K hK ∈ horn.carrier \ K :=
  (Classical.choose_spec (horn.exists_unique_escaping_component K hK)).1

theorem escapingComponent_contains_tail (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ horn.coordinateTail b ⊆ horn.escapingComponent K hK := by
  obtain ⟨b, hb0, hb1, htail, _, _⟩ :=
    (Classical.choose_spec (horn.exists_unique_escaping_component K hK)).2
  exact ⟨b, hb0, hb1, htail⟩

theorem escapingComponent_not_subset_compact (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K)
    (L : Set (E.extended.slice T).carrier) (hL : IsCompact L) :
    ¬ horn.escapingComponent K hK ⊆ L := by
  obtain ⟨_, _, _, _, hescape, _⟩ :=
    (Classical.choose_spec (horn.exists_unique_escaping_component K hK)).2
  exact hescape L hL

theorem escapingComponent_eq_of_not_subset_compact (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K)
    (x : (E.extended.slice T).carrier)
    (hx : ∀ L : Set (E.extended.slice T).carrier, IsCompact L →
      ¬ connectedComponentIn (horn.carrier \ K) x ⊆ L) :
    connectedComponentIn (horn.carrier \ K) x = horn.escapingComponent K hK := by
  obtain ⟨_, _, _, _, _, huniq⟩ :=
    (Classical.choose_spec (horn.exists_unique_escaping_component K hK)).2
  exact huniq x hx

theorem escapingComponent_subset (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    horn.escapingComponent K hK ⊆ horn.carrier \ K :=
  connectedComponentIn_subset _ _

theorem escapingComponent_isConnected (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    IsConnected (horn.escapingComponent K hK) :=
  isConnected_connectedComponentIn_iff.mpr (horn.escapingPoint_mem K hK)


theorem component_subset_prefix_of_ne_escaping (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K)
    (x : (E.extended.slice T).carrier)
    (hx : connectedComponentIn (horn.carrier \ K) x ≠ horn.escapingComponent K hK) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      connectedComponentIn (horn.carrier \ K) x ⊆ horn.coordinatePrefix b := by
  obtain ⟨b, hb0, hb1, htail⟩ := horn.escapingComponent_contains_tail K hK
  refine ⟨b, hb0, hb1, ?_⟩
  intro y hy
  rcases horn.carrier_subset_prefix_union_tail b
    (connectedComponentIn_subset _ _ hy).1 with hp | ht
  · exact hp
  · exact False.elim (hx ((connectedComponentIn_eq hy).trans
      (connectedComponentIn_eq (htail ht)).symm))

end PoincareConjecture.StrongHorn
