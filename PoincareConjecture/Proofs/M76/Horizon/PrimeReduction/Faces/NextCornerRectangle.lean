import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.NormalCornerAdjacency
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBoundaryCollarTopology









set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner




theorem exists_next_corner_component_rectangle
    {ι : Type*} [Finite ι] (D : ι → Set (ℝ × ℝ)) (p q : ι → ℝ × ℝ)
    (hD : ∀ k, IsFinitePLBallPair ℝ (D k) {p k, q k})
    (hsub : ∀ k, D k ⊆ base)
    (hrim : ∀ k, ({p k, q k} : Set (ℝ × ℝ)) = D k ∩ frontier base)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hleft : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ {0} ×ˢ Icc (0 : ℝ) 1)
    (hbottom : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ Icc (0 : ℝ) 1 ×ˢ {0})
    (i : ι) {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hi : ({p i, q i} : Set (ℝ × ℝ)) = {(0, b), (a, 0)})
    (hnext : ∃ k, ∃ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (0 : ℝ) 1,
      ({p k, q k} : Set (ℝ × ℝ)) = {(0, y), (x, 0)} ∧ a < x) :
    ∃ j, ∃ c ∈ Ioo (0 : ℝ) 1, ∃ d ∈ Ioo (0 : ℝ) 1,
      i ≠ j ∧ ({p j, q j} : Set (ℝ × ℝ)) = {(0, d), (c, 0)} ∧ a < c ∧
      ∃ M : Set (ℝ × ℝ),
        IsFinitePLBallPair (ℝ × ℝ) M (D i ∪ (D j ∪ edgeIntervals a b c d)) ∧
        M ∩ frontier base = edgeIntervals a b c d ∧
        (∀ k, k ≠ i → k ≠ j → Disjoint (D k) M) ∧
        (∀ x ∈ M \ (D i ∪ D j),
          connectedComponentIn (base \ ⋃ k, D k) x = M \ (D i ∪ D j) ∧
          closure (connectedComponentIn (base \ ⋃ k, D k) x) = M) ∧
        ∃ C : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M,
          C.IsFinitePL ∧
          (∀ x, (C x : ℝ × ℝ) ∈ D i ↔ (x : ℝ × ℝ).2 = 0) ∧
          (∀ x, (C x : ℝ × ℝ) ∈ D j ↔ (x : ℝ × ℝ).2 = 1) ∧
          (∀ x, (C x : ℝ × ℝ) ∈ ({0} ×ˢ Icc b d) ↔ (x : ℝ × ℝ).1 = 0) ∧
          (∀ x, (C x : ℝ × ℝ) ∈ (Icc a c ×ˢ {0}) ↔ (x : ℝ × ℝ).1 = 1) := by
  obtain ⟨j, c, hc, d, hd, hj, hac, hadj⟩ := exists_next_corner_pair p q a hnext
  have hne : i ≠ j := by
    intro heij
    have hec := horizontalEndpoint_eq hd.1.ne' hj
    rw [← heij, horizontalEndpoint_eq hb.1.ne' hi] at hec
    exact hac.ne hec
  have hboundary := boundary_adjacency_of_no_intermediate_pair D p q
    (fun k => (hD k).1) hdis hleft hbottom i j ha hb hc hd hi hj hadj
  obtain ⟨M, hM, hMB, hother, hcomponent, C, hC, hCW, hCZ, hCL, hCR⟩ :=
    exists_component_rectangle_of_boundary_adjacency D (fun k => {p k, q k}) hD
      hsub hrim hdis i j hne ha hb hc hd hi hj hac hboundary
  refine ⟨j, c, hc, d, hd, hne, hj, hac, M, hM, hMB, hother, ?_, C, hC,
    hCW, hCZ, hCL, hCR⟩
  intro x hx
  refine ⟨hcomponent x hx, ?_⟩
  rw [hcomponent x hx]
  apply hM.closure_sdiff_of_subset_boundary
  exact union_subset subset_union_left (subset_union_left.trans subset_union_right)

end PoincareConjecture.M76.TriangleCorner
