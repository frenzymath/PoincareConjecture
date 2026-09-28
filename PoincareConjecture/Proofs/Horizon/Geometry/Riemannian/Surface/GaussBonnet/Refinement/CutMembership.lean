import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Incidence








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface


theorem affineCutPoint_eq_reverse_of_mul_neg (f : Plane →ᵃ[ℝ] ℝ)
    (a b : Plane) (hcross : f a * f b < 0) :
    affineCutPoint f a b = affineCutPoint f b a := by
  rcases mul_neg_iff.mp hcross with h | h
  · exact affineCutPoint.eq_reverse f a b h.1 h.2
  · exact (affineCutPoint.eq_reverse f b a h.2 h.1).symm

private theorem strict_cut_mem (f : Plane →ᵃ[ℝ] ℝ) (p : Fin 3 → Plane)
    (h01 : f (p 0) * f (p 1) < 0) (h02 : f (p 0) * f (p 2) < 0)
    (h12 : 0 ≤ f (p 1) * f (p 2))
    (i j : Fin 3) (hcross : f (p i) * f (p j) < 0) :
    affineCutPoint f (p i) (p j) ∈
      [affineCutPoint f (p 0) (p 1), affineCutPoint f (p 0) (p 2)] := by
  have h10 := affineCutPoint_eq_reverse_of_mul_neg f (p 0) (p 1) h01
  have h20 := affineCutPoint_eq_reverse_of_mul_neg f (p 0) (p 2) h02
  fin_cases i <;> fin_cases j <;>
    norm_num only at hcross <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] <;>
    first | exact Or.inl rfl | exact Or.inr rfl |
      exact Or.inl h10.symm | exact Or.inr h20.symm |
      exact False.elim (not_lt_of_ge h12 hcross) |
      exact False.elim (not_lt_of_ge (by simpa [mul_comm] using h12) hcross) | nlinarith

private theorem edge_cut_mem (f : Plane →ᵃ[ℝ] ℝ) (p : Fin 3 → Plane)
    (h01 : f (p 0) * f (p 1) < 0) (h2 : f (p 2) = 0)
    (i j : Fin 3) (hcross : f (p i) * f (p j) < 0) :
    affineCutPoint f (p i) (p j) ∈ [affineCutPoint f (p 0) (p 1)] := by
  have h10 := affineCutPoint_eq_reverse_of_mul_neg f (p 0) (p 1) h01
  have h02 : 0 ≤ f (p 0) * f (p 2) := by rw [h2, mul_zero]
  have h12 : 0 ≤ f (p 1) * f (p 2) := by rw [h2, mul_zero]
  have h20 : 0 ≤ f (p 2) * f (p 0) := by rw [h2, zero_mul]
  have h21 : 0 ≤ f (p 2) * f (p 1) := by rw [h2, zero_mul]
  fin_cases i <;> fin_cases j <;> norm_num only at hcross <;>
    simp only [List.mem_singleton] <;>
    first | rfl | exact h10.symm | nlinarith |
      exact False.elim (not_lt_of_ge h02 hcross) |
      exact False.elim (not_lt_of_ge h12 hcross) |
      exact False.elim (not_lt_of_ge h20 hcross) |
      exact False.elim (not_lt_of_ge h21 hcross)

private theorem crossing_has_ordering (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ)
    (t : M.Triangle) (i j : Fin 3)
    (hcross : f (M.position (M.orderedVertex t i)) *
      f (M.position (M.orderedVertex t j)) < 0) :
    Nonempty (M.PositiveStrictOrdering f t) ∨ Nonempty (M.NegativeStrictOrdering f t) ∨
      Nonempty (M.PositiveEdgeOrdering f t) ∨ Nonempty (M.NegativeEdgeOrdering f t) := by
  have hdistinct : i ≠ j := by
    rintro rfl
    exact (not_lt_of_ge (mul_self_nonneg _)) hcross
  obtain ⟨e, he0, he1⟩ : ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j := by
    exact (by decide : ∀ i j : Fin 3, i ≠ j →
      ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j) i j hdistinct
  rw [← he0, ← he1] at hcross
  rcases mul_neg_iff.mp hcross with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rcases lt_trichotomy (f (M.position (M.orderedVertex t (e 2)))) 0 with h2 | h2 | h2
    · exact Or.inl ⟨⟨e, h0, h1, h2⟩⟩
    · exact Or.inr (Or.inr (Or.inl ⟨⟨e, h0, h1, h2⟩⟩))
    · apply Or.inr ∘ Or.inl
      refine ⟨⟨(Equiv.swap 0 1).trans e, ?_, ?_, ?_⟩⟩
      · simpa [Equiv.trans_apply, Equiv.swap_apply_def] using h1
      · simpa [Equiv.trans_apply, Equiv.swap_apply_def] using h0
      · simpa [Equiv.trans_apply, Equiv.swap_apply_def] using h2
  · rcases lt_trichotomy (f (M.position (M.orderedVertex t (e 2)))) 0 with h2 | h2 | h2
    · apply Or.inl
      refine ⟨⟨(Equiv.swap 0 1).trans e, ?_, ?_, ?_⟩⟩
      · simpa [Equiv.trans_apply, Equiv.swap_apply_def] using h1
      · simpa [Equiv.trans_apply, Equiv.swap_apply_def] using h0
      · simpa [Equiv.trans_apply, Equiv.swap_apply_def] using h2
    · exact Or.inr (Or.inr (Or.inr ⟨⟨e, h0, h1, h2⟩⟩))
    · exact Or.inr (Or.inl ⟨⟨e, h0, h1, h2⟩⟩)



theorem affineCutPoint_mem_localRefinementBoundaryCuts (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {a b : M.Vertex}
    (ha : a ∈ t.1) (hb : b ∈ t.1)
    (hcross : f (M.position a) * f (M.position b) < 0) :
    affineCutPoint f (M.position a) (M.position b) ∈
      localRefinementBoundaryCuts M f t := by
  obtain ⟨i, rfl⟩ := (M.range_orderedVertex t ▸ ha : a ∈ range (M.orderedVertex t))
  obtain ⟨j, rfl⟩ := (M.range_orderedVertex t ▸ hb : b ∈ range (M.orderedVertex t))
  unfold localRefinementBoundaryCuts
  split_ifs with hp hn hep hen
  · let o := Classical.choice hp
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      strict_cut_mem f (M.position ∘ M.orderedVertex t ∘ o.perm)
        (mul_neg_of_pos_of_neg o.positive o.negative_one)
        (mul_neg_of_pos_of_neg o.positive o.negative_two)
        (mul_nonneg_of_nonpos_of_nonpos o.negative_one.le o.negative_two.le)
        (o.perm.symm i) (o.perm.symm j) (by simpa using hcross)
  · let o := Classical.choice hn
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      strict_cut_mem f (M.position ∘ M.orderedVertex t ∘ o.perm)
        (mul_neg_of_neg_of_pos o.negative o.positive_one)
        (mul_neg_of_neg_of_pos o.negative o.positive_two)
        (mul_nonneg o.positive_one.le o.positive_two.le)
        (o.perm.symm i) (o.perm.symm j) (by simpa using hcross)
  · let o := Classical.choice hep
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      edge_cut_mem f (M.position ∘ M.orderedVertex t ∘ o.perm)
        (mul_neg_of_pos_of_neg o.positive o.negative) o.zero
        (o.perm.symm i) (o.perm.symm j) (by simpa using hcross)
  · let o := Classical.choice hen
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      edge_cut_mem f (M.position ∘ M.orderedVertex t ∘ o.perm)
        (mul_neg_of_neg_of_pos o.negative o.positive) o.zero
        (o.perm.symm i) (o.perm.symm j) (by simpa using hcross)
  · exact False.elim ((crossing_has_ordering M f t i j hcross).elim hp
      (fun h => h.elim hn (fun h => h.elim hep hen)))



theorem mem_localRefinementBoundaryCuts_iff_crossed_edge (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane} :
    q ∈ localRefinementBoundaryCuts M f t ↔
      ∃ a ∈ t.1, ∃ b ∈ t.1, f (M.position a) * f (M.position b) < 0 ∧
        q = affineCutPoint f (M.position a) (M.position b) := by
  constructor
  · exact localRefinementBoundaryCuts_crossed_edge M f t
  · rintro ⟨a, ha, b, hb, hcross, rfl⟩
    exact affineCutPoint_mem_localRefinementBoundaryCuts M f t ha hb hcross



theorem localRefinementBoundaryCuts_mem_of_mem_hull (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t) (u : M.Triangle)
    (hu : q ∈ convexHull ℝ (range (meshTriangleBasis M u))) :
    q ∈ localRefinementBoundaryCuts M f u := by
  obtain ⟨a, ha, b, hb, hcross, rfl⟩ := localRefinementBoundaryCuts_crossed_edge M f t hq
  have hab : a ≠ b := by
    rintro rfl
    exact (not_lt_of_ge (mul_self_nonneg _)) hcross
  have hseg := affineCutPoint_mem_openSegment_of_mul_neg f _ _ hcross
  have huab := mesh_edge_endpoints_mem_of_openSegment_mem_hull M t u ha hb hab hseg hu
  exact affineCutPoint_mem_localRefinementBoundaryCuts M f u huab.1 huab.2 hcross



theorem localRefinementBoundaryCuts_mem_iff_mem_hull (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t) (u : M.Triangle) :
    q ∈ localRefinementBoundaryCuts M f u ↔
      q ∈ convexHull ℝ (range (meshTriangleBasis M u)) := by
  constructor
  · intro hqu
    exact ((finite_range _).isClosed_convexHull ℝ).frontier_subset
      (localRefinementBoundaryCuts_geometry M f u hqu).1
  · exact localRefinementBoundaryCuts_mem_of_mem_hull M f t hq u

end PoincareConjecture.Topology.Surface
