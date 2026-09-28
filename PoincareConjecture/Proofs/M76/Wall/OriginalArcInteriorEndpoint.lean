import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteContactEdgeVertex











set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76






theorem exists_original_arc_edge_interior_endpoint
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {C L : Set X} (hL : IsClosed L) {q : ℝ → X}
    (hzero : q 0 ∈ frontier L) (hone : q 1 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L)
    (hqC : MapsTo q (Icc (0 : ℝ) 1) (interior C))
    (K A D : SimplicialComplex ℝ E) (hAK : A ≤ K) (hDK : D ≤ K)
    (hfull : ∀ t ∈ K.faces, (∀ p ∈ t, p ∈ D.vertices) → t ∈ D.faces)
    (hfinite : (A.space ∩ D.space).Finite) (g : E → X)
    (hgarc : MapsTo g A.space (q '' Icc (0 : ℝ) 1))
    (hfront : ∀ z ∈ A.space, g z ∈ frontier L → z ∈ D.space)
    {s : Finset E} (hs : s ∈ A.faces) (hcard : s.card = 2) :
    ∃ p ∈ s, g p ∈ interior (C \ interior L) := by
  obtain ⟨p, hps, hpD⟩ :=
    exists_edge_vertex_outside_of_finite_contact hAK hfull hfinite hs hcard
  have hpA : p ∈ A.space := A.subset_space hs hps
  have hgpfront : g p ∉ frontier L := by
    intro h
    exact hpD (mem_vertices_of_finite_subcomplex_intersection hAK hDK hfinite
      hpA (hfront p hpA h)).2
  obtain ⟨t, ht, hgt⟩ := hgarc hpA
  have ht0 : t ≠ 0 := by
    intro he
    apply hgpfront
    rw [← hgt, he]
    exact hzero
  have ht1 : t ≠ 1 := by
    intro he
    apply hgpfront
    rw [← hgt, he]
    exact hone
  have hgpL : g p ∉ L := by
    rw [← hgt]
    exact hproper t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  have hgpC : g p ∈ interior C := hgt ▸ hqC ht
  have hopen : IsOpen (interior C \ L) := isOpen_interior.sdiff hL
  have hsub : interior C \ L ⊆ C \ interior L :=
    fun _ hx => ⟨interior_subset hx.1, fun hy => hx.2 (interior_subset hy)⟩
  exact ⟨p, hps, interior_maximal hsub hopen ⟨hgpC, hgpL⟩⟩

end PoincareConjecture.M76
