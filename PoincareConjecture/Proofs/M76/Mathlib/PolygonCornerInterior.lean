import PoincareConjecture.Proofs.M76.Mathlib.PolygonCornerCap
import PoincareConjecture.Proofs.M76.Mathlib.PolygonPreconnectedRegion
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSupportingHeight
import PoincareConjecture.Proofs.M76.Mathlib.LocalQuadrantRegion










set_option autoImplicit false

open Set Filter
open scoped Topology

private theorem mem_axis_corner_iff {q : ℝ × ℝ} (hx : q.1 ≤ 1) (hy : q.2 ≤ 1) :
    q ∈ segment ℝ (1, 0) (0, 0) ∪ segment ℝ (0, 0) (0, 1) ↔
      0 ≤ q.1 ∧ 0 ≤ q.2 ∧ (q.1 = 0 ∨ q.2 = 0) := by
  constructor
  · rintro (hq | hq)
    · have hp := Prod.segment_subset (𝕜 := ℝ) (1, 0) (0, 0) hq
      norm_num [segment_eq_uIcc] at hp
      exact ⟨hp.1.1, by rw [hp.2], Or.inr hp.2⟩
    · have hp := Prod.segment_subset (𝕜 := ℝ) (0, 0) (0, 1) hq
      norm_num [segment_eq_uIcc] at hp
      exact ⟨by rw [hp.1], hp.2.1, Or.inl hp.1⟩
  · rintro ⟨hqx, hqy, hzero | hzero⟩
    · right
      refine ⟨1 - q.2, q.2, by linarith, hqy, by ring, ?_⟩
      ext <;> simp [hzero]
    · left
      refine ⟨q.1, 1 - q.1, hqx, by linarith, by ring, ?_⟩
      ext <;> simp [hzero]

namespace Polygon




theorem exists_positive_square_inside_corner {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (i : Fin (n + 3))
    (hprev : P ((finRotate (n + 3)).symm i) = (1, 0)) (hcenter : P i = (0, 0))
    (hnext : P (finRotate (n + 3) i) = (0, 1))
    (hnegative : ∀ t : ℝ, 0 < t → (-t, -t) ∈ P.outside) :
    ∃ δ : ℝ, 0 < δ ∧ Ioo 0 δ ×ˢ Ioo 0 δ ⊆ P.inside := by
  apply exists_positive_square_subset_region (P.isOpen_outside hP hinj) (P.isOpen_inside hP hinj)
    P.disjoint_inside_outside.symm
    (by rw [P.compl_boundary_eq_inside_union_outside, union_comm]) _ _ hnegative
  · rw [← hcenter]
    apply frontier_subset_closure
    rw [P.frontier_inside hP hinj]
    exact mem_iUnion.mpr ⟨i, left_mem_affineSegment ℝ _ _⟩
  · have hlocal := P.eventually_boundary_iff_adjacent_edges hP hinj i
    rw [hcenter] at hlocal
    have hcoord : ∀ᶠ q : ℝ × ℝ in 𝓝 (0, 0), q.1 < 1 ∧ q.2 < 1 :=
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_snd continuous_const)).mem_nhds (by norm_num)
    filter_upwards [hlocal, hcoord] with q hq hc
    rw [hq, edgeSet, edgeSet, Equiv.apply_symm_apply, hprev, hcenter, hnext,
      affineSegment_eq_segment, affineSegment_eq_segment]
    exact mem_axis_corner_iff hc.1.le hc.2.le




theorem corner_cap_subset_inside {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (i : Fin (n + 3))
    (hprev : P ((finRotate (n + 3)).symm i) = (1, 0)) (hcenter : P i = (0, 0))
    (hnext : P (finRotate (n + 3) i) = (0, 1))
    (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hL : ∀ j, L (P j) ≤ 0) (hdir : 0 < L (-1, -1))
    {h : ℝ} (hpos : 0 < h) (hle : h ≤ 1)
    (hvertices : ∀ j, ¬ (0 < (P j).1 ∧ 0 < (P j).2 ∧ (P j).1 + (P j).2 < h)) :
    {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < h} ⊆ P.inside := by
  obtain ⟨δ, hδ, hsquare⟩ := P.exists_positive_square_inside_corner hP hinj i hprev hcenter hnext
    (P.negative_diagonal_mem_outside L hL hdir)
  have hdis := P.disjoint_boundary_corner_cap hP hinj i hprev hcenter hnext hle hvertices
  have hconv : Convex ℝ {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < h} :=
    ((convex_Ioi (𝕜 := ℝ) 0).linear_preimage (LinearMap.fst ℝ ℝ ℝ)).inter
      (((convex_Ioi (𝕜 := ℝ) 0).linear_preimage (LinearMap.snd ℝ ℝ ℝ)).inter
        ((convex_Iio (𝕜 := ℝ) h).linear_preimage
          (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ)))
  apply P.subset_inside_of_preconnected_inter hconv.isPreconnected
    (fun _ hq hb => Set.disjoint_left.mp hdis hq hb)
  let t := min δ h / 4
  have ht : 0 < t := div_pos (lt_min hδ hpos) (by norm_num)
  have htδ : t < δ := by dsimp [t]; linarith [min_le_left δ h]
  have hth : t + t < h := by dsimp [t]; linarith [min_le_right δ h]
  exact ⟨(t, t), ⟨ht, ht, hth⟩, hsquare ⟨⟨ht, htδ⟩, ht, htδ⟩⟩

end Polygon
