import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryFootStarContainment











set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in




theorem original_endpoint_foot_subset_sphere
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {L C : Set X} (hL : IsClosed L) (hLC : L ⊆ C)
    (K D : SimplicialComplex ℝ E) [Fintype D.faces] (hDK : D ≤ K)
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (F : X → E) (hHF : ∀ y : C, (H y : E) = F y)
    (hD : D.space = F '' frontier L)
    (U S : Fin 2 → Set X)
    (hUS : ∀ i, U i ∩ frontier L ⊆ S i)
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    {i : Fin 2} {a : X} (ha : a ∈ frontier L) (haS : a ∈ S i)
    {p : E} (hpD : p ∈ D.vertices) (hp : p = F a)
    (hstar : ∃ G : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space G.source ∧
      (G.source ⊆ Lᶜ ∨ ∃ j : Fin 2, G.source ⊆ U j))
    {c : E → E}
    (hmarks : ∀ J : SimplicialComplex ℝ E, J ≤ K → c '' J.space = J.space) :
    c '' (D.barycentricDualBlock {p}).space ⊆ F '' S i ∧
      MapsTo (fun z => (g z : X)) (c '' (D.barycentricDualBlock {p}).space) (S i) := by
  classical
  have hgF (x : X) (hx : x ∈ C) : (g (F x) : X) = x := by
    have heq := hg (H ⟨x, hx⟩)
    rw [H.symm_apply_apply] at heq
    simpa only [hHF] using heq
  have hFg (z : K.space) : F (g z) = (z : E) := by
    calc
      F (g z) = F (H.symm z) := congrArg F (hg z)
      _ = (H (H.symm z) : E) := (hHF (H.symm z)).symm
      _ = (z : E) := by rw [H.apply_symm_apply]
  have hpK : p ∈ K.vertices := hDK hpD
  have hpstar : p ∈ (K.closedStar p).space := by
    apply (K.closedStar p).vertices_subset_space
    exact ⟨hpK, by
      simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)] using
        (K.mem_vertices.mp hpK)⟩
  have hgp : (g p : X) = a := by
    rw [hp]
    exact hgF a (hLC (hL.frontier_subset ha))
  obtain ⟨G, hsource, hbranch⟩ := hstar
  have haG : a ∈ G.source := by
    have hmem := hsource hpstar
    change (g p : X) ∈ G.source at hmem
    rwa [hgp] at hmem
  have hGU : G.source ⊆ U i := by
    rcases hbranch with haway | ⟨j, hGU⟩
    · exact False.elim ((haway haG) (hL.frontier_subset ha))
    · have haj : a ∈ S j := hUS j ⟨hGU haG, ha⟩
      have hji : j = i := by
        by_contra hne
        exact disjoint_left.mp (hdisjoint hne) haj haS
      simpa only [hji] using hGU
  have hcontain := K.image_vertex_dual_subset_original_star_and_mark D hDK hpD hmarks
  have hwhole : MapsTo (fun z => (g z : X))
      (c '' (D.barycentricDualBlock {p}).space) (S i) := by
    intro z hz
    have hzG : (g z : X) ∈ G.source := hsource (hcontain hz).1
    have hzfront : (g z : X) ∈ frontier L := by
      obtain ⟨x, hx, hFx⟩ := hD.subset (hcontain hz).2
      rw [← hFx, hgF x (hLC (hL.frontier_subset hx))]
      exact hx
    exact hUS i ⟨hGU hzG, hzfront⟩
  refine ⟨?_, hwhole⟩
  intro z hz
  exact ⟨g z, hwhole hz, hFg ⟨z, space_subset_of_le hDK (hcontain hz).2⟩⟩

end PoincareConjecture.M76
