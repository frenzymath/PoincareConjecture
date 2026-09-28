


import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.Subdivision.Vertices
import Mathlib.Analysis.Normed.Affine.AddTorsorBases









namespace Poincare.Topology.Plane.Meshes

open Set

namespace TriangleMesh


theorem lineRefinementMesh_vertex_old_or_zero (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (v : (M.lineRefinementMesh f).Vertex) :
    (M.lineRefinementMesh f).position v ∈ range M.position ∨
      f ((M.lineRefinementMesh f).position v) = 0 := by
  classical
  have hv := v.2
  change v.1 ∈ M.refinementPoints f at hv
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hv
    exact Or.inl ⟨w, hw⟩
  · obtain ⟨⟨u, w⟩, huw, hv⟩ := Finset.mem_image.mp hv
    right
    change f v.1 = 0
    rw [← hv]
    exact M.pairCutPosition_apply_eq_zero f u w (Finset.mem_filter.mp huw).2


theorem refineByLines_boundary_vertices_subset (M : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) (B S : Set Plane)
    (hM : range M.position ∩ B ⊆ S)
    (hlines : ∀ f ∈ lines, B ∩ {p | f p = 0} ⊆ S) :
    range (M.refineByLines lines).position ∩ B ⊆ S := by
  induction lines generalizing M with
  | nil => exact hM
  | cons f fs ih =>
      apply ih (M.lineRefinementMesh f)
      · rintro p ⟨⟨v, rfl⟩, hp⟩
        rcases M.lineRefinementMesh_vertex_old_or_zero f v with hv | hv
        · exact hM ⟨hv, hp⟩
        · exact hlines f (by simp) ⟨hp, hv⟩
      · exact fun g hg => hlines g (by simp [hg])

end TriangleMesh

private theorem coord_nonneg_of_mem_triangle (b : AffineBasis (Fin 3) ℝ Plane)
    {p : Plane} (hp : p ∈ convexHull ℝ (range b)) (i : Fin 3) :
    0 ≤ b.coord i p := by
  have h : ∀ j, 0 ≤ b.coord j p := by
    simpa only [b.convexHull_eq_nonneg_coord, mem_ofPred_eq] using hp
  exact h i

private theorem exists_coord_eq_zero_of_mem_frontier
    (b : AffineBasis (Fin 3) ℝ Plane) {p : Plane}
    (hp : p ∈ frontier (convexHull ℝ (range b))) :
    ∃ i : Fin 3, b.coord i p = 0 := by
  have hclosed := ((finite_range b).isCompact_convexHull ℝ).isClosed
  have hnonneg := coord_nonneg_of_mem_triangle b (hclosed.frontier_subset hp)
  by_contra! h
  have hint : p ∈ interior (convexHull ℝ (range b)) := by
    rw [b.interior_convexHull]
    exact fun i => lt_of_le_of_ne (hnonneg i) (h i).symm
  exact hp.2 hint

private theorem range_reindex_swap (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) :
    range (b.reindex (Equiv.swap 0 i)) = range b := by
  change range (b ∘ (Equiv.swap 0 i).symm) = range b
  exact (Equiv.swap 0 i).symm.surjective.range_comp b

private theorem triangle_basis_ext (b : AffineBasis (Fin 3) ℝ Plane) {x y : Plane}
    (h0 : b.coord 0 x = b.coord 0 y) (h1 : b.coord 1 x = b.coord 1 y)
    (h2 : b.coord 2 x = b.coord 2 y) : x = y := by
  apply b.ext_elem
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem exists_cevian_at_zero_coord
    (b : AffineBasis (Fin 3) ℝ Plane) {p : Plane}
    (hp : p ∈ convexHull ℝ (range b)) (hp0 : b.coord 0 p = 0)
    (hpv : p ∉ range b) :
    ∃ f g : Plane →ᵃ[ℝ] ℝ,
      (∀ y ∈ convexHull ℝ (range b), 0 ≤ g y) ∧ g p = 0 ∧ f p = 0 ∧
      (∀ y, g y = 0 → f y = 0 → y = p) ∧
      frontier (convexHull ℝ (range b)) ∩ {y | f y = 0} ⊆ {p} ∪ range b := by
  have hsum (y : Plane) : b.coord 0 y + b.coord 1 y + b.coord 2 y = 1 := by
    have h := b.sum_coord_apply_eq_one y
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change b.coord 0 y + (b.coord 1 y + b.coord 2 y) = 1 at h
    linarith
  have hp1 : 0 < b.coord 1 p := by
    by_contra! h
    have hp1 := le_antisymm h (coord_nonneg_of_mem_triangle b hp 1)
    have hpeq : p = b 2 := by
      apply triangle_basis_ext b
      · simpa using hp0
      · simpa using hp1
      · simpa using (show b.coord 2 p = 1 by linarith [hsum p])
    exact hpv ⟨2, hpeq.symm⟩
  have hp2 : 0 < b.coord 2 p := by
    by_contra! h
    have hp2 := le_antisymm h (coord_nonneg_of_mem_triangle b hp 2)
    have hpeq : p = b 1 := by
      apply triangle_basis_ext b
      · simpa using hp0
      · simpa using (show b.coord 1 p = 1 by linarith [hsum p])
      · simpa using hp2
    exact hpv ⟨1, hpeq.symm⟩
  let f : Plane →ᵃ[ℝ] ℝ := b.coord 2 p • b.coord 1 - b.coord 1 p • b.coord 2
  have hf (y : Plane) : f y = b.coord 2 p * b.coord 1 y -
      b.coord 1 p * b.coord 2 y := rfl
  have hunique : ∀ y, b.coord 0 y = 0 → f y = 0 → y = p := by
    intro y hy0 hyf
    rw [hf] at hyf
    have hy1 : b.coord 1 y = b.coord 1 p := by nlinarith [hsum p, hsum y]
    apply triangle_basis_ext b
    · exact hy0.trans hp0.symm
    · exact hy1
    · linarith [hsum p, hsum y]
  refine ⟨f, b.coord 0, fun y hy => coord_nonneg_of_mem_triangle b hy 0,
    hp0, ?_, hunique, ?_⟩
  · rw [hf]
    ring
  · rintro y ⟨hy, hyf⟩
    change f y = 0 at hyf
    obtain ⟨i, hi⟩ := exists_coord_eq_zero_of_mem_frontier b hy
    fin_cases i
    · exact Or.inl (hunique y hi hyf)
    · right
      change b.coord 1 y = 0 at hi
      have hy2 : b.coord 2 y = 0 := by
        rw [hf, hi, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at hyf
        exact hyf.resolve_left (ne_of_gt hp1)
      refine ⟨0, ?_⟩
      apply triangle_basis_ext b
      · simpa using (show 1 = b.coord 0 y by linarith [hsum y])
      · simpa using hi.symm
      · simpa using hy2.symm
    · right
      change b.coord 2 y = 0 at hi
      have hy1 : b.coord 1 y = 0 := by
        rw [hf, hi, mul_zero, sub_zero, mul_eq_zero] at hyf
        exact hyf.resolve_left (ne_of_gt hp2)
      refine ⟨0, ?_⟩
      apply triangle_basis_ext b
      · simpa using (show 1 = b.coord 0 y by linarith [hsum y])
      · simpa using hy1.symm
      · simpa using hi.symm

private theorem exists_boundary_cevian
    (b : AffineBasis (Fin 3) ℝ Plane) {p : Plane}
    (hp : p ∈ frontier (convexHull ℝ (range b))) (hpv : p ∉ range b) :
    ∃ f g : Plane →ᵃ[ℝ] ℝ,
      (∀ y ∈ convexHull ℝ (range b), 0 ≤ g y) ∧ g p = 0 ∧ f p = 0 ∧
      (∀ y, g y = 0 → f y = 0 → y = p) ∧
      frontier (convexHull ℝ (range b)) ∩ {y | f y = 0} ⊆ {p} ∪ range b := by
  classical
  obtain ⟨i, hi⟩ := exists_coord_eq_zero_of_mem_frontier b hp
  let c := b.reindex (Equiv.swap 0 i)
  have hrange : range c = range b := range_reindex_swap b i
  have hc0 : c.coord 0 p = 0 := by
    simpa only [c, AffineBasis.coord_reindex, Equiv.symm_swap, Equiv.swap_apply_left] using hi
  have hpc : p ∈ convexHull ℝ (range c) := by
    rw [hrange]
    exact ((finite_range b).isCompact_convexHull ℝ).isClosed.frontier_subset hp
  simpa only [hrange] using exists_cevian_at_zero_coord c hpc hc0 (by simpa [hrange] using hpv)

private theorem isMonochromatic_of_nonneg_on_support (N : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (hf : ∀ y ∈ N.toPlaneComplex.support, 0 ≤ f y) :
    N.IsMonochromatic f := by
  intro t ht
  left
  intro v hv
  apply hf
  rw [N.toPlaneComplex_support]
  exact mem_iUnion₂.mpr ⟨t, ht, subset_convexHull ℝ _ ⟨v, hv, rfl⟩⟩

private theorem exists_vertex_supporting_functions
    (b : AffineBasis (Fin 3) ℝ Plane) {p : Plane} (hp : p ∈ range b) :
    ∃ f g : Plane →ᵃ[ℝ] ℝ,
      (∀ y ∈ convexHull ℝ (range b), 0 ≤ f y) ∧
      (∀ y ∈ convexHull ℝ (range b), 0 ≤ g y) ∧ f p = 0 ∧ g p = 0 ∧
      (∀ y, f y = 0 → g y = 0 → y = p) := by
  classical
  obtain ⟨i, rfl⟩ := hp
  let c := b.reindex (Equiv.swap 0 i)
  have hrange : range c = range b := range_reindex_swap b i
  have hc0 : c 0 = b i := by simp [c]
  refine ⟨c.coord 1, c.coord 2, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact coord_nonneg_of_mem_triangle c (by rwa [hrange]) 1
  · intro y hy
    exact coord_nonneg_of_mem_triangle c (by rwa [hrange]) 2
  · rw [← hc0]
    simp
  · rw [← hc0]
    simp
  · intro y hy1 hy2
    rw [← hc0]
    apply triangle_basis_ext c
    · have hsum := c.sum_coord_apply_eq_one y
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
      change c.coord 0 y + (c.coord 1 y + c.coord 2 y) = 1 at hsum
      simpa using (show c.coord 0 y = 1 by linarith)
    · simpa using hy1
    · simpa using hy2



theorem exists_triangleMesh_exact_boundary_vertices_with_refinement
    (b : AffineBasis (Fin 3) ℝ Plane) (S : Finset Plane)
    (hS : (S : Set Plane) ⊆ frontier (convexHull ℝ (Set.range b)))
    (hvertices : Set.range b ⊆ (S : Set Plane)) :
    ∃ N : TriangleMesh,
      N.toPlaneComplex.support = convexHull ℝ (Set.range b) ∧
      Set.range N.position ∩ frontier (convexHull ℝ (Set.range b)) =
        (S : Set Plane) ∧
      (∀ (p : Plane), p ∈ S →
        ∀ (t : Finset N.Vertex), t ∈ N.triangles →
          p ∈ N.toPlaneComplex.cellCarrier t →
            p ∈ N.position '' (t : Set N.Vertex)) ∧
      N.toPlaneComplex.Subdivides (TriangleMesh.single b b.ind).toPlaneComplex ∧
      ∃ lines : List (Plane →ᵃ[ℝ] ℝ),
        N = (TriangleMesh.single b b.ind).refineByLines lines := by
  classical
  let P : Finset Plane := S.filter fun p => p ∉ range b
  have hcuts (p : {p // p ∈ P}) :
      ∃ f g : Plane →ᵃ[ℝ] ℝ,
        (∀ y ∈ convexHull ℝ (range b), 0 ≤ g y) ∧ g p = 0 ∧ f p = 0 ∧
        (∀ y, g y = 0 → f y = 0 → y = p) ∧
        frontier (convexHull ℝ (range b)) ∩ {y | f y = 0} ⊆ {p.1} ∪ range b := by
    have hp := Finset.mem_filter.mp p.2
    exact exists_boundary_cevian b (hS hp.1) hp.2
  choose f g hg_nonneg hg_zero hf_zero h_unique h_frontier using hcuts
  let lines : List (Plane →ᵃ[ℝ] ℝ) :=
    (Finset.univ : Finset {p // p ∈ P}).toList.map f
  let N := (TriangleMesh.single b b.ind).refineByLines lines
  have hsupport : N.toPlaneComplex.support = convexHull ℝ (range b) := by
    dsimp only [N]
    rw [TriangleMesh.refineByLines_support, TriangleMesh.single_support]
  have hmark (p : Plane) (hp : p ∈ S) (t : Finset N.Vertex)
      (ht : t ∈ N.triangles) (hpt : p ∈ N.toPlaneComplex.cellCarrier t) :
      p ∈ N.position '' (t : Set N.Vertex) := by
    by_cases hpv : p ∈ range b
    · obtain ⟨f, g, hf, hg, hfp, hgp, huniq⟩ := exists_vertex_supporting_functions b hpv
      have hfN : N.IsMonochromatic f := isMonochromatic_of_nonneg_on_support N f
        (by simpa only [hsupport] using hf)
      have hgN : N.IsMonochromatic g := isMonochromatic_of_nonneg_on_support N g
        (by simpa only [hsupport] using hg)
      exact N.mem_triangle_vertices_of_monochromatic hfN hgN hfp hgp huniq ht hpt
    · let q : {p // p ∈ P} := ⟨p, Finset.mem_filter.mpr ⟨hp, hpv⟩⟩
      have hfmem : f q ∈ lines := by simp [lines]
      have hfN : N.IsMonochromatic (f q) :=
        (TriangleMesh.single b b.ind).refineByLines_isMonochromatic_of_mem lines hfmem
      have hgN : N.IsMonochromatic (g q) := isMonochromatic_of_nonneg_on_support N (g q)
        (by simpa only [hsupport] using hg_nonneg q)
      exact N.mem_triangle_vertices_of_monochromatic hgN hfN
        (hg_zero q) (hf_zero q) (h_unique q) ht hpt
  have hboundary : range N.position ∩ frontier (convexHull ℝ (range b)) ⊆
      (S : Set Plane) := by
    apply (TriangleMesh.single b b.ind).refineByLines_boundary_vertices_subset lines
    · rintro p ⟨hp, -⟩
      exact hvertices hp
    · intro h hh
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hh
      intro y hy
      rcases h_frontier p hy with hy | hy
      · have hy : y = p.1 := hy
        rw [hy]
        exact (Finset.mem_filter.mp p.2).1
      · exact hvertices hy
  refine ⟨N, hsupport, subset_antisymm hboundary ?_, hmark,
    (TriangleMesh.single b b.ind).refineByLines_subdivides lines, lines, rfl⟩
  intro p hp
  have hpfront := hS hp
  have hpsupport : p ∈ N.toPlaneComplex.support := by
    rw [hsupport]
    exact ((finite_range b).isCompact_convexHull ℝ).isClosed.frontier_subset hpfront
  rw [N.toPlaneComplex_support] at hpsupport
  obtain ⟨t, ht, hpt⟩ := mem_iUnion₂.mp hpsupport
  obtain ⟨v, -, hv⟩ := hmark p hp t ht hpt
  exact ⟨⟨v, hv⟩, hpfront⟩


theorem exists_triangleMesh_exact_boundary_vertices
    (b : AffineBasis (Fin 3) ℝ Plane) (S : Finset Plane)
    (hS : (S : Set Plane) ⊆ frontier (convexHull ℝ (Set.range b)))
    (hvertices : Set.range b ⊆ (S : Set Plane)) :
    ∃ N : TriangleMesh,
      N.toPlaneComplex.support = convexHull ℝ (Set.range b) ∧
      Set.range N.position ∩ frontier (convexHull ℝ (Set.range b)) =
        (S : Set Plane) ∧
      (∀ (p : Plane), p ∈ S →
        ∀ (t : Finset N.Vertex), t ∈ N.triangles →
          p ∈ N.toPlaneComplex.cellCarrier t →
            p ∈ N.position '' (t : Set N.Vertex)) ∧
      N.toPlaneComplex.Subdivides (TriangleMesh.single b b.ind).toPlaneComplex := by
  obtain ⟨N, hs, hb, hm, hd, _⟩ :=
    exists_triangleMesh_exact_boundary_vertices_with_refinement b S hS hvertices
  exact ⟨N, hs, hb, hm, hd⟩

end Poincare.Topology.Plane.Meshes
