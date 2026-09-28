import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.ComponentCharts









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry

namespace PoincareConjecture.M76

open Classical in
theorem exists_whole_component_family_of_finite_model
    {X E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : X → E) (g : E → X) {S : Set X}
    (hFc : Continuous F) (hFi : Function.Injective F)
    (hKs : K.space = F '' S) (hgc : ContinuousOn g K.space)
    (hgi : InjOn g K.space) (hFg : ∀ z ∈ K.space, F (g z) = z)
    (hgS : g '' K.space = S) :
    ∃ (n : ℕ) (T : Fin n → Set X),
      (⋃ i, T i) = S ∧ Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      ∀ i, IsCompact (T i) ∧ IsPathConnected (T i) ∧
        (∀ x ∈ T i, connectedComponentIn S x = T i) ∧
        ∃ O : Set X, IsOpen O ∧ T i = S ∩ O := by
  classical
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  let I := K.vertexAbstractComplex.edgeGraph.ConnectedComponent
  let : Fintype I := Fintype.ofFinite I
  let U (i : I) := g '' (K.edgeComponentComplex i).space
  have hsub (i : I) : (K.edgeComponentComplex i).space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le i)
  have hUS (i : I) : U i ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact hgS.subset ⟨z, hsub i hz, rfl⟩
  have hUK (i : I) : IsCompact (U i) :=
    ((K.edgeComponentComplex i).isCompact_space_of_finite
      (hK.subset (K.edgeComponentComplex_le i))).image_of_continuousOn (hgc.mono (hsub i))
  have hUconn (i : I) : IsPathConnected (U i) :=
    (K.edgeComponentComplex_isPathConnected i).image' (hgc.mono (hsub i))
  have hUcover : (⋃ i, U i) = S := by
    change (⋃ i, g '' (K.edgeComponentComplex i).space) = _
    rw [← image_iUnion, K.iUnion_edgeComponentComplex_space]
    exact hgS
  have hUdis : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have heq := hgi (hsub j hw) (hsub i hz) hwz
    exact disjoint_left.mp (K.pairwise_disjoint_edgeComponentComplex_space hij) hz (heq ▸ hw)
  have hFK (y : X) (hy : y ∈ S) : F y ∈ K.space := hKs.symm.subset ⟨y, hy, rfl⟩
  have hgF (y : X) (hy : y ∈ S) : g (F y) = y := hFi (hFg (F y) (hFK y hy))
  have hcomponent (i : I) (x : X) (hx : x ∈ U i) : connectedComponentIn S x = U i := by
    apply Subset.antisymm
    · have hxS := hUS i hx
      have hxP : F x ∈ (K.edgeComponentComplex i).space := by
        obtain ⟨z, hz, rfl⟩ := hx
        rw [hFg z (hsub i hz)]
        exact hz
      have hm := hFc.continuousOn.image_connectedComponentIn_subset hxS
      rw [← hKs, HamiltonIntervalTorus.edgeComponentComplex_connectedComponentIn K hK i hxP] at hm
      intro y hy
      exact ⟨F y, hm ⟨y, hy, rfl⟩, hgF y (connectedComponentIn_subset S x hy)⟩
    · exact (hUconn i).isConnected.isPreconnected.subset_connectedComponentIn hx (hUS i)
  have hopen (i : I) : ∃ O : Set X, IsOpen O ∧ U i = S ∩ O := by
    obtain ⟨O, hO, heq⟩ := exists_open_edge_component_neighborhood K hK i
    refine ⟨F ⁻¹' O, hO.preimage hFc, ?_⟩
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hgS.subset ⟨z, hsub i hz, rfl⟩,
        by change F (g z) ∈ O; rw [hFg z (hsub i hz)]; exact (heq.symm.subset hz).2⟩
    · rintro ⟨hxS, hxO⟩
      exact ⟨F x, heq.subset ⟨hFK x hxS, hxO⟩, hgF x hxS⟩
  let r := Fintype.equivFin I
  refine ⟨Fintype.card I, fun i => U (r.symm i), ?_, ?_, ?_⟩
  · calc
      (⋃ i, U (r.symm i)) = ⋃ i, U i := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          exact mem_iUnion.mpr ⟨r.symm i, hi⟩
        · intro hx
          obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          exact mem_iUnion.mpr ⟨r i, by simpa using hi⟩
      _ = S := hUcover
  · intro i j hij
    exact hUdis (fun h => hij (r.symm.injective h))
  · intro i
    exact ⟨hUK (r.symm i), hUconn (r.symm i), hcomponent (r.symm i), hopen (r.symm i)⟩

end PoincareConjecture.M76
