import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.FrontierAvoidsFinite
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFacetInterior
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialGenerators









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem exists_exposed_edge_of_pure_triangles (K : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 2) (hK : K.faces.Finite)
    (hne : K.faces.Nonempty)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3) :
    ∃ e ∈ K.faces, e.card = 2 ∧
      ∃ t ∈ K.faces, t.card = 3 ∧ e ⊆ t ∧
        ∀ u ∈ K.faces, u.card = 3 → e ⊆ u → u = t := by
  classical
  obtain ⟨s, hs⟩ := hne
  obtain ⟨t, ht, _, htcard⟩ := hpure s hs
  have htne : (convexHull ℝ (t : Set E)).Nonempty := by
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ht
    exact ⟨v, subset_convexHull ℝ (t : Set E) hv⟩
  obtain ⟨y, hy⟩ := htne.intrinsicInterior (convex_convexHull ℝ _)
  have hinterior : (interior K.space).Nonempty :=
    ⟨y, K.mem_interior_space_of_full_face ht (by omega) hy⟩
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank, hdim]
    norm_num
  obtain ⟨x, hxfront, hxv⟩ :=
    Poincare.Topology.IsCompact.exists_frontier_not_mem_finite
      (K.isCompact_space_of_finite hK) hinterior
      (K.finite_vertices_of_finite_faces hK) hrank
  have hxK : x ∈ K.space := (K.isCompact_space_of_finite hK).isClosed.closure_subset
    (frontier_subset_closure hxfront)
  obtain ⟨e, he, hxe⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
  obtain ⟨t, ht, het, htcard⟩ := hpure e he
  have hle : e.card ≤ 3 := htcard ▸ Finset.card_le_card het
  have hpos : 0 < e.card := (K.nonempty_of_mem_faces he).card_pos
  have hnotone : e.card ≠ 1 := by
    intro hone
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
    have hx : x = v := by
      simpa using (intrinsicInterior_subset hxe)
    subst x
    exact hxv (mem_vertices.mpr he)
  have hnotthree : e.card ≠ 3 := by
    intro hthree
    exact hxfront.2
      (K.mem_interior_space_of_full_face he (by omega) hxe)
  have hecard : e.card = 2 := by omega
  refine ⟨e, he, hecard, t, ht, htcard, het, ?_⟩
  intro u hu hucard heu
  by_contra hne
  exact hxfront.2
    (K.mem_interior_space_of_paired_facet (by omega) ht hu (by omega)
      (by omega) het heu (Ne.symm hne) hxe)



theorem exists_exposed_edge_of_triangle_selection (K : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 2) (hK : K.faces.Finite)
    (F : Set (Finset E)) (hFK : F ⊆ K.faces) (hne : F.Nonempty)
    (hcard : ∀ t ∈ F, t.card = 3) :
    ∃ e ∈ K.faces, e.card = 2 ∧
      ∃ t ∈ F, e ⊆ t ∧ ∀ u ∈ F, e ⊆ u → u = t := by
  classical
  let hind := fun (t : Finset E) (ht : t ∈ F) => K.indep (hFK ht)
  let hinter := fun (t : Finset E) (ht : t ∈ F) (u : Finset E) (hu : u ∈ F) =>
    K.inter_subset_convexHull (hFK ht) (hFK hu)
  let J := ofGenerators F hind hinter
  have hJK : J ≤ K := by
    rintro s ⟨hs, t, ht, hst⟩
    exact K.down_closed (hFK ht) hst hs
  have hgen : ∀ t ∈ F, t ∈ J.faces := by
    intro t ht
    exact ⟨K.nonempty_of_mem_faces (hFK ht), t, ht, Finset.Subset.refl _⟩
  have hJne : J.faces.Nonempty := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨t, hgen t ht⟩
  have hpure : ∀ s ∈ J.faces, ∃ t ∈ J.faces, s ⊆ t ∧ t.card = 3 := by
    rintro s ⟨_, t, ht, hst⟩
    exact ⟨t, hgen t ht, hst, hcard t ht⟩
  obtain ⟨e, he, hecard, t, ht, htcard, het, huniq⟩ :=
    J.exists_exposed_edge_of_pure_triangles hdim (hK.subset hJK) hJne hpure
  obtain ⟨_, u, hu, htu⟩ := ht
  have htuEq : t = u := Finset.eq_of_subset_of_card_le htu (by rw [htcard, hcard u hu])
  subst u
  exact ⟨e, hJK he, hecard, t, hu, het,
    fun u hu heu => huniq u (hgen u hu) (hcard u hu) heu⟩

end Geometry.SimplicialComplex
