import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RetainedCoreMatching













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open Poincare.Topology.Plane.Meshes PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem exists_uniform_minimum
    {X : Type*} (f : Fin 3 → X → ℝ) (K : Set X)
    (horder : ∀ i j, (∀ x ∈ K, f i x ≤ f j x) ∨ (∀ x ∈ K, f j x ≤ f i x)) :
    ∃ i, ∀ j x, x ∈ K → f i x ≤ f j x := by
  rcases horder 0 1 with h01 | h10
  · rcases horder 0 2 with h02 | h20
    · refine ⟨0, ?_⟩
      intro j x hx
      fin_cases j
      · exact le_rfl
      · exact h01 x hx
      · exact h02 x hx
    · refine ⟨2, ?_⟩
      intro j x hx
      fin_cases j
      · exact h20 x hx
      · exact (h20 x hx).trans (h01 x hx)
      · exact le_rfl
  · rcases horder 1 2 with h12 | h21
    · refine ⟨1, ?_⟩
      intro j x hx
      fin_cases j
      · exact h10 x hx
      · exact le_rfl
      · exact h12 x hx
    · refine ⟨2, ?_⟩
      intro j x hx
      fin_cases j
      · exact (h21 x hx).trans (h10 x hx)
      · exact h21 x hx
      · exact le_rfl

private theorem parent_edge_eq_coord_zero
    (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) :
    convexHull ℝ (range b) ∩ {z | b.coord i z = 0} =
      affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) := by
  rw [convexHull_inter_affine_zero_of_nonneg_set (range b) (b.coord i)
    (by rintro z ⟨j, rfl⟩; rw [b.coord_apply]; split_ifs <;> norm_num)]
  rw [affineSegment_eq_segment, ← convexHull_pair]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨j, rfl⟩, hj⟩
    have hji : j ≠ i := by intro h; subst j; simp at hj
    fin_cases i <;> fin_cases j <;> simp_all [Fin.succAbove, Fin.lt_def, Fin.ext_iff]
  · rintro (rfl | rfl)
    · refine ⟨mem_range_self _, ?_⟩
      fin_cases i <;> simp [Fin.succAbove, Fin.lt_def, Fin.ext_iff]
    · refine ⟨mem_range_self _, ?_⟩
      fin_cases i <;> simp [Fin.succAbove, Fin.lt_def, Fin.ext_iff]






theorem m64Intrinsic_parent_boundary_one_edge_of_coord_order
    (b : AffineBasis (Fin 3) ℝ Plane) {K : Set Plane}
    (hK : K ⊆ convexHull ℝ (range b))
    (horder : ∀ i j, (∀ x ∈ K, b.coord i x ≤ b.coord j x) ∨
      (∀ x ∈ K, b.coord j x ≤ b.coord i x)) :
    ∃ i : Fin 3, K ∩ frontier (convexHull ℝ (range b)) ⊆
      affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) := by
  obtain ⟨i, hi⟩ := exists_uniform_minimum (fun j x => b.coord j x) K horder
  refine ⟨i, ?_⟩
  rintro x ⟨hxK, hxfront⟩
  have hxparent := hK hxK
  have hnonneg : ∀ j, 0 ≤ b.coord j x := by
    simpa only [b.convexHull_eq_nonneg_coord, mem_ofPred_eq] using hxparent
  have hnot : ¬ ∀ j, 0 < b.coord j x := by
    simpa only [b.interior_convexHull, mem_ofPred_eq] using hxfront.2
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  have hzero : b.coord i x = 0 :=
    le_antisymm ((hi j x hxK).trans (not_lt.mp hj)) (hnonneg i)
  rw [← parent_edge_eq_coord_zero b i]
  exact ⟨hxparent, hzero⟩







theorem m64Intrinsic_parent_vertices_unique_of_coord_order
    (b : AffineBasis (Fin 3) ℝ Plane) {K : Set Plane}
    (horder : ∀ i j, (∀ x ∈ K, b.coord i x ≤ b.coord j x) ∨
      (∀ x ∈ K, b.coord j x ≤ b.coord i x))
    (i j : Fin 3) (hi : b i ∈ K) (hj : b j ∈ K) : i = j := by
  by_contra hij
  rcases horder i j with hle | hge
  · have h := hle (b i) hi
    norm_num [b.coord_apply, Ne.symm hij] at h
  · have h := hge (b j) hj
    norm_num [b.coord_apply, hij] at h







theorem m64Intrinsic_exists_parent_boundary_refinement
    (b : AffineBasis (Fin 3) ℝ Plane) :
    ∃ M : TriangleMesh,
      M.toPlaneComplex.support = convexHull ℝ (range b) ∧
      M.toPlaneComplex.Subdivides (TriangleMesh.single b b.ind).toPlaneComplex ∧
      (∀ t : M.Triangle, ∃ i : Fin 3,
        M.triangleCarrier t.1 ∩ frontier (convexHull ℝ (range b)) ⊆
          affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1))) ∧
      (∀ (t : M.Triangle) (i j : Fin 3),
        b i ∈ M.triangleCarrier t.1 → b j ∈ M.triangleCarrier t.1 → i = j) := by
  classical
  let lines := (Finset.univ : Finset (Fin 3 × Fin 3)).toList.map
    (fun p => b.coord p.1 - b.coord p.2)
  let M := (TriangleMesh.single b b.ind).refineByLines lines
  have hsupport : M.toPlaneComplex.support = convexHull ℝ (range b) := by
    rw [TriangleMesh.refineByLines_support, TriangleMesh.single_support]
  have horder (t : M.Triangle) (i j : Fin 3) :
      (∀ x ∈ M.triangleCarrier t.1, b.coord i x ≤ b.coord j x) ∨
        (∀ x ∈ M.triangleCarrier t.1, b.coord j x ≤ b.coord i x) := by
    have hmem : b.coord i - b.coord j ∈ lines := by
      apply List.mem_map.mpr
      exact ⟨(i, j), by simp, rfl⟩
    have hmono := (TriangleMesh.single b b.ind).refineByLines_isMonochromatic_of_mem
      lines hmem
    rcases hmono.triangleCarrier_halfspace M t with hnonneg | hnonpos
    · right
      intro x hx
      exact sub_nonneg.mp (hnonneg x hx)
    · left
      intro x hx
      exact sub_nonpos.mp (hnonpos x hx)
  refine ⟨M, hsupport, (TriangleMesh.single b b.ind).refineByLines_subdivides lines, ?_, ?_⟩
  · intro t
    apply m64Intrinsic_parent_boundary_one_edge_of_coord_order b ?_ (horder t)
    intro x hx
    rw [← hsupport, TriangleMesh.toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨t.1, t.2, hx⟩
  · intro t i j hi hj
    exact m64Intrinsic_parent_vertices_unique_of_coord_order b (horder t) i j hi hj

end PoincareConjecture
