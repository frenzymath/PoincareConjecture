import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.TriangleCornerSymmetries










set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

theorem frontier_point_edge_cases {p : ℝ × ℝ}
    (hp : p ∈ frontier base) (hv : p ∉ vertices) :
    (p.1 = 0 ∧ p.2 ∈ Ioo (0 : ℝ) 1) ∨
      (p.2 = 0 ∧ p.1 ∈ Ioo (0 : ℝ) 1) ∨
      (p.1 + p.2 = 1 ∧ p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1) := by
  have hpbase := isFinitePLBallPair_base.1 hp
  rw [base_eq_triangle, TriangleDiskModel.mem_right_region_iff] at hpbase
  have hz : roof p = 0 := frontier_base.subset hp
  have hne0 : p ≠ (0, 0) := fun he => hv (by simp [vertices, he])
  have hne1 : p ≠ (1, 0) := fun he => hv (by simp [vertices, he])
  have hne2 : p ≠ (0, 1) := fun he => hv (by simp [vertices, he])
  by_cases hpx : p.1 = 0
  · refine Or.inl ⟨hpx, ?_, ?_⟩
    · exact lt_of_le_of_ne hpbase.2.1 (fun he => hne0 (Prod.ext hpx he.symm))
    · have hle : p.2 ≤ 1 := by linarith [hpbase.2.2]
      exact lt_of_le_of_ne hle (fun he => hne2 (Prod.ext hpx he))
  by_cases hpy : p.2 = 0
  · refine Or.inr (Or.inl ⟨hpy, ?_, ?_⟩)
    · exact lt_of_le_of_ne hpbase.1 (fun he => hpx he.symm)
    · have hle : p.1 ≤ 1 := by linarith [hpbase.2.2]
      exact lt_of_le_of_ne hle (fun he => hne1 (Prod.ext he hpy))
  have hxpos := lt_of_le_of_ne hpbase.1 (fun he => hpx he.symm)
  have hypos := lt_of_le_of_ne hpbase.2.1 (fun he => hpy he.symm)
  have hsum : p.1 + p.2 = 1 := by
    apply le_antisymm hpbase.2.2
    by_contra hn
    have hdiag : 0 < 1 - p.1 - p.2 := by linarith
    have hroof : 0 < roof p := lt_min hxpos (lt_min hypos hdiag)
    exact (hz ▸ hroof).false
  exact Or.inr (Or.inr ⟨hsum, ⟨hxpos, by linarith⟩, hypos, by linarith⟩)

private theorem pair_eq_of_points {p q p' q' : ℝ × ℝ} (hp : p = p') (hq : q = q') :
    ({p, q} : Set (ℝ × ℝ)) = {p', q'} := congrArg₂ (fun x y => ({x, y} : Set (ℝ × ℝ))) hp hq



theorem exists_unique_normal_corner {p q : ℝ × ℝ}
    (hp : p ∈ frontier base) (hq : q ∈ frontier base)
    (hpv : p ∉ vertices) (hqv : q ∉ vertices)
    (hleft : ¬ ({p, q} : Set (ℝ × ℝ)) ⊆ {0} ×ˢ Icc (0 : ℝ) 1)
    (hbottom : ¬ ({p, q} : Set (ℝ × ℝ)) ⊆ Icc (0 : ℝ) 1 ×ˢ {0})
    (hdiagonal : ¬ ({p, q} : Set (ℝ × ℝ)) ⊆ {x ∈ base | x.1 + x.2 = 1}) :
    ∃! c : Fin 3, ∃ a ∈ Ioo (0 : ℝ) 1, ∃ b ∈ Ioo (0 : ℝ) 1,
      cornerMap c '' ({p, q} : Set (ℝ × ℝ)) = {(0, b), (a, 0)} := by
  have hex : ∃ c : Fin 3, ∃ a ∈ Ioo (0 : ℝ) 1, ∃ b ∈ Ioo (0 : ℝ) 1,
      cornerMap c '' ({p, q} : Set (ℝ × ℝ)) = {(0, b), (a, 0)} := by
    rcases frontier_point_edge_cases hp hpv with hp | hp | hp <;>
      rcases frontier_point_edge_cases hq hqv with hq | hq | hq
    · exfalso
      apply hleft
      rintro x (rfl | rfl)
      · exact ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
      · exact ⟨hq.1, hq.2.1.le, hq.2.2.le⟩
    · refine ⟨0, q.1, hq.2, p.2, hp.2, ?_⟩
      simp only [image_insert_eq, image_singleton, cornerMap_zero]
      exact pair_eq_of_points (Prod.ext hp.1 rfl) (Prod.ext rfl hq.1)
    · refine ⟨2, q.1, hq.2.1, 1 - p.2, ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩, ?_⟩
      simp only [image_insert_eq, image_singleton, cornerMap_two]
      apply pair_eq_of_points
      · exact Prod.ext hp.1 (by linarith [hp.1])
      · exact Prod.ext rfl (by linarith [hq.1])
    · refine ⟨0, p.1, hp.2, q.2, hq.2, ?_⟩
      simp only [image_insert_eq, image_singleton, cornerMap_zero]
      rw [pair_comm]
      exact pair_eq_of_points (Prod.ext hq.1 rfl) (Prod.ext rfl hp.1)
    · exfalso
      apply hbottom
      rintro x (rfl | rfl)
      · exact ⟨⟨hp.2.1.le, hp.2.2.le⟩, hp.1⟩
      · exact ⟨⟨hq.2.1.le, hq.2.2.le⟩, hq.1⟩
    · refine ⟨1, 1 - p.1, ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩, q.2, hq.2.2, ?_⟩
      simp only [image_insert_eq, image_singleton, cornerMap_one]
      rw [pair_comm]
      apply pair_eq_of_points
      · exact Prod.ext (by linarith [hq.1]) rfl
      · exact Prod.ext (by linarith [hp.1]) hp.1
    · refine ⟨2, p.1, hp.2.1, 1 - q.2, ⟨by linarith [hq.2.2], by linarith [hq.2.1]⟩, ?_⟩
      simp only [image_insert_eq, image_singleton, cornerMap_two]
      rw [pair_comm]
      apply pair_eq_of_points
      · exact Prod.ext hq.1 (by linarith [hq.1])
      · exact Prod.ext rfl (by linarith [hp.1])
    · refine ⟨1, 1 - q.1, ⟨by linarith [hq.2.2], by linarith [hq.2.1]⟩, p.2, hp.2.2, ?_⟩
      simp only [image_insert_eq, image_singleton, cornerMap_one]
      apply pair_eq_of_points
      · exact Prod.ext (by linarith [hp.1]) rfl
      · exact Prod.ext (by linarith [hq.1]) hq.1
    · exfalso
      apply hdiagonal
      rintro x (rfl | rfl)
      · exact ⟨isFinitePLBallPair_base.1 (show x ∈ frontier base by assumption), hp.1⟩
      · exact ⟨isFinitePLBallPair_base.1 (show x ∈ frontier base by assumption), hq.1⟩
  obtain ⟨c, a, ha, b, hb, hc⟩ := hex
  refine ⟨c, ⟨a, ha, b, hb, hc⟩, ?_⟩
  rintro d ⟨u, hu, v, hv, hd⟩
  exact (corner_pair_unique ha hb hc hd).symm

end PoincareConjecture.M76.TriangleCorner
