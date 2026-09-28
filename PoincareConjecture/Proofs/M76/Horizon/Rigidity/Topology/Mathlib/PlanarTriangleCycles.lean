import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.PlanarExposedEdge
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTetrahedronAdjacency
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleChainCoordinates

set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem exists_exposed_vertex_edge_of_triangle_selection (K : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 2) (hK : K.faces.Finite)
    (B : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex → Prop)
    (hne : ∃ t, B t) :
    ∃ e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
      ∃ t, B t ∧ e.val ⊆ t.val ∧ ∀ u, B u → e.val ⊆ u.val → u = t := by
  classical
  let : DecidableEq K.vertices := Classical.decEq _
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let F : Set (Finset E) := {s | ∃ t : Triangle A, B t ∧ (K.vertexFaceEquiv 3 t).val = s}
  have hFK : F ⊆ K.faces := by
    rintro s ⟨t, _, rfl⟩
    exact (K.vertexFaceEquiv 3 t).property.1
  have hFne : F.Nonempty := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨_, t, ht, rfl⟩
  have hFcard : ∀ t ∈ F, t.card = 3 := by
    rintro s ⟨t, _, rfl⟩
    exact (K.vertexFaceEquiv 3 t).property.2
  obtain ⟨e, he, hecard, s, hs, hes, huniq⟩ :=
    K.exists_exposed_edge_of_triangle_selection hdim hK F hFK hFne hFcard
  obtain ⟨t, ht, rfl⟩ := hs
  let e' : Edge A := (K.vertexFaceEquiv 2).symm ⟨e, he, hecard⟩
  have hmap : e'.val.map (Function.Embedding.subtype _) = e :=
    K.vertexFaceEquiv_symm_map 2 ⟨e, he, hecard⟩
  have het : e'.val ⊆ t.val := by
    apply Finset.map_subset_map.mp
    rw [hmap]
    exact hes
  refine ⟨e', t, ht, het, ?_⟩
  intro u hu heu
  apply (K.vertexFaceEquiv 3).injective
  apply Subtype.ext
  apply huniq _ ⟨u, hu, rfl⟩
  change e ⊆ u.val.map (Function.Embedding.subtype _)
  rw [← hmap]
  exact Finset.map_subset_map.mpr heu

theorem boundary2_ker_eq_bot_of_planar (K : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 2) (hK : K.faces.Finite) [Fintype K.vertices] :
    LinearMap.ker (edgeCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex).dualMap
      = ⊥ := by
  classical
  let : DecidableEq K.vertices := Classical.decEq _
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  have hzero : ∀ t : Triangle A, c (Pi.single t 1) = 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨e, t, ht, het, huniq⟩ :=
      K.exists_exposed_vertex_edge_of_triangle_selection hdim hK
        (fun t => c (Pi.single t 1) ≠ 0) hn
    have hsum := boundary2_single_eq_sum_coordinates A c e
    have hsum' : (∑ u ∈ triangleCofaces A e, c (Pi.single u 1)) = c (Pi.single t 1) := by
      apply Finset.sum_eq_single t
      · intro u hu hut
        by_contra hnonzero
        have heu : e.val ⊆ u.val := (Finset.mem_filter.mp hu).2
        exact hut (huniq u hnonzero heu)
      · intro htmem
        exact False.elim (htmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, het⟩))
    rw [hsum'] at hsum
    rw [hc] at hsum
    exact ht hsum.symm
  have heq := triangleChain_eq_smul_total_of_coordinates A c 0 hzero
  simpa using heq

end Geometry.SimplicialComplex
