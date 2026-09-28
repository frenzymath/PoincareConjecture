import PoincareConjecture.Proofs.M76.Mathlib.PolygonPathCycles
import PoincareConjecture.Proofs.M76.Mathlib.PolygonDiagonalPartition
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDisk











set_option autoImplicit false

open Set

namespace Polygon





theorem crossingIndex_three_paths {m n k : ℕ}
    (u : Fin (m + 2) → ℝ × ℝ) (v : Fin (n + 2) → ℝ × ℝ)
    (w : Fin (k + 2) → ℝ × ℝ)
    (huv : u (Fin.last (m + 1)) = v 0)
    (hvu : v (Fin.last (n + 1)) = u 0)
    (hwu : w 0 = u 0) (hwv : w (Fin.last (k + 1)) = v 0)
    (q : ℝ × ℝ) :
    (ofPaths u v).crossingIndex q =
      (ofPaths u (fun i => w i.rev)).crossingIndex q +
        (ofPaths w v).crossingIndex q := by
  exact Fin.cyclicEdgeSum_three_paths (fun a b => PlanarSegment.crossingContribution a b q)
    (fun a b => PlanarSegment.crossingContribution_swap a b q) u v w huv hvu hwu hwv








theorem region_partition_three_paths {m n k : ℕ}
    (u : Fin (m + 4) → ℝ × ℝ) (v : Fin (n + 4) → ℝ × ℝ)
    (w : Fin (k + 4) → ℝ × ℝ)
    (huv : u (Fin.last (m + 3)) = v 0)
    (hvu : v (Fin.last (n + 3)) = u 0)
    (hwu : w 0 = u 0) (hwv : w (Fin.last (k + 3)) = v 0)
    (hP : (ofPaths u v).HasSimplicialEdges) (hiP : Function.Injective (ofPaths u v))
    (hQ : (ofPaths u (fun i => w i.rev)).HasSimplicialEdges)
    (hiQ : Function.Injective (ofPaths u (fun i => w i.rev)))
    (hR : (ofPaths w v).HasSimplicialEdges) (hiR : Function.Injective (ofPaths w v))
    (hwP : pathCarrier w ⊆ closure (ofPaths u v).inside)
    (hinter : pathCarrier u ∩ pathCarrier v ⊆ pathCarrier w) :
    Disjoint (ofPaths u (fun i => w i.rev)).inside (ofPaths w v).inside ∧
      closure (ofPaths u v).inside =
        closure (ofPaths u (fun i => w i.rev)).inside ∪ closure (ofPaths w v).inside ∧
      closure (ofPaths u (fun i => w i.rev)).inside ∩ closure (ofPaths w v).inside =
        pathCarrier w := by
  let P := ofPaths u v
  let Q := ofPaths u (fun i => w i.rev)
  let R := ofPaths w v
  have huv' : u (Fin.last (m + 3)) = (fun i : Fin (k + 4) => w i.rev) 0 := by
    simpa only [Fin.rev_zero] using huv.trans hwv.symm
  have hvu' : (fun i => w i.rev) (Fin.last (k + 3)) = u 0 := by
    simpa only [Fin.rev_last] using hwu
  have hPb : P.boundary ℝ = pathCarrier u ∪ pathCarrier v := boundary_ofPaths u v huv hvu
  have hQb : Q.boundary ℝ = pathCarrier u ∪ pathCarrier w := by
    dsimp only [Q]
    rw [boundary_ofPaths u (fun i => w i.rev) huv' hvu', pathCarrier_reverse]
  have hRb : R.boundary ℝ = pathCarrier w ∪ pathCarrier v :=
    boundary_ofPaths w v hwv (hvu.trans hwu.symm)
  have hBP : P.boundary ℝ ⊆ closure P.inside := by
    rw [← P.frontier_inside hP hiP]
    exact frontier_subset_closure
  have hQP : Q.boundary ℝ ⊆ closure P.inside := by
    rw [hQb]
    exact union_subset (fun x hx => hBP (hPb.symm ▸ Or.inl hx)) hwP
  have hRP : R.boundary ℝ ⊆ closure P.inside := by
    rw [hRb]
    exact union_subset hwP (fun x hx => hBP (hPb.symm ▸ Or.inr hx))
  have hcover : P.boundary ℝ ⊆ Q.boundary ℝ ∪ R.boundary ℝ := by
    rw [hPb, hQb, hRb]
    exact fun x hx => hx.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inr h))
  have hcommon : Q.boundary ℝ ∩ R.boundary ℝ = pathCarrier w := by
    rw [hQb, hRb]
    ext x
    constructor
    · rintro ⟨hu | hw, hw' | hv⟩
      · exact hw'
      · exact hinter ⟨hu, hv⟩
      · exact hw
      · exact hw
    · exact fun hx => ⟨Or.inr hx, Or.inl hx⟩
  have hfinite := (finite_range P).union ((finite_range Q).union (finite_range R))
  obtain ⟨e, he⟩ := hfinite.exists_planar_coordinates_injOn_fst
  let f := e.toLinearEquiv.toAffineEquiv.toAffineMap
  have hnv {l : ℕ} (S : Polygon (ℝ × ℝ) (l + 3)) (hiS : Function.Injective S)
      (hS : range S ⊆ range P ∪ (range Q ∪ range R)) :
      (S.affineImage f).HasNonverticalEdges := by
    apply hasNonverticalEdges_of_injective_fst _ (by omega)
    intro i j hij
    exact hiS (he (hS (mem_range_self i)) (hS (mem_range_self j)) hij)
  have hmap {a b : ℕ} (s : Fin (a + 1) → ℝ × ℝ) (t : Fin (b + 1) → ℝ × ℝ) :
      ofPaths (e ∘ s) (e ∘ t) = (ofPaths s t).affineImage f := by
    change mk (Fin.append (Fin.init (e ∘ s)) (Fin.init (e ∘ t))) =
      mk (e ∘ Fin.append (Fin.init s) (Fin.init t))
    apply congrArg mk
    funext i
    induction i using Fin.addCases <;> simp [Fin.init, Function.comp_def]
  have hsum (q : ℝ × ℝ) : (P.affineImage f).crossingIndex q =
      (Q.affineImage f).crossingIndex q + (R.affineImage f).crossingIndex q := by
    rw [show P = ofPaths u v from rfl, show Q = ofPaths u (fun i => w i.rev) from rfl,
      show R = ofPaths w v from rfl, ← hmap, ← hmap, ← hmap]
    exact crossingIndex_three_paths (e ∘ u) (e ∘ v) (e ∘ w)
      (congrArg e huv) (congrArg e hvu) (congrArg e hwu) (congrArg e hwv) q
  obtain ⟨hdis, hwhole⟩ := region_partition_of_index_sum
    (P.affineImage f) (Q.affineImage f) (R.affineImage f)
    (P.hasSimplicialEdges_affineImage hP f e.injective) (e.injective.comp hiP)
    (hnv P hiP subset_union_left)
    (Q.hasSimplicialEdges_affineImage hQ f e.injective) (e.injective.comp hiQ)
    (hnv Q hiQ (subset_union_left.trans subset_union_right))
    (R.hasSimplicialEdges_affineImage hR f e.injective) (e.injective.comp hiR)
    (hnv R hiR (subset_union_right.trans subset_union_right))
    (by rw [affineImage_boundary, closure_inside_linearImage]; exact image_mono hQP)
    (by rw [affineImage_boundary, closure_inside_linearImage]; exact image_mono hRP)
    (by simp only [affineImage_boundary, ← image_union]; exact image_mono hcover) hsum
  rw [inside_linearImage, inside_linearImage] at hdis
  have hdis' : Disjoint Q.inside R.inside := (disjoint_image_iff e.injective).mp hdis
  refine ⟨hdis', ?_, ?_⟩
  · apply (image_injective.mpr e.injective)
    rw [P.closure_inside_linearImage e, Q.closure_inside_linearImage e,
      R.closure_inside_linearImage e] at hwhole
    simpa only [image_union] using hwhole
  · rw [Q.closure_inside_inter_eq_boundary_inter R hQ hiQ hR hiR hdis', hcommon]

end Polygon
