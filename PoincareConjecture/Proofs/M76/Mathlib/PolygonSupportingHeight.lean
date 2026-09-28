import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionNesting

set_option autoImplicit false

open Set

namespace Polygon

theorem affine_height_le_on_boundary {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (P : Polygon E n) (L : E →ᵃ[ℝ] ℝ) {c : ℝ}
    (hL : ∀ i, L (P i) ≤ c) : ∀ q ∈ P.boundary ℝ, L q ≤ c := by
  intro q hq
  obtain ⟨i, hi⟩ := mem_iUnion.mp hq
  have himg := mem_image_of_mem L hi
  rw [edgeSet, affineSegment_eq_segment, image_segment, segment_eq_uIcc] at himg
  exact himg.2.trans (max_le (hL i) (hL (finRotate n i)))

theorem negative_diagonal_mem_outside {n : ℕ} (P : Polygon (ℝ × ℝ) n)
    (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hL : ∀ i, L (P i) ≤ 0)
    (hdir : 0 < L (-1, -1)) (t : ℝ) (ht : 0 < t) : (-t, -t) ∈ P.outside := by
  let S : Set (ℝ × ℝ) := (fun s : ℝ => (-s, -s)) '' Ioi 0
  have hconn : IsPreconnected S :=
    isPreconnected_Ioi.image _ (continuous_neg.prodMk continuous_neg).continuousOn
  have hsub : S ⊆ (P.boundary ℝ)ᶜ := by
    rintro _ ⟨s, hs, rfl⟩ hboundary
    have hb := P.affine_height_le_on_boundary L.toAffineMap hL _ hboundary
    have hvec : ((-s, -s) : ℝ × ℝ) = s • ((-1 : ℝ), (-1 : ℝ)) := by
      ext <;> simp [smul_eq_mul]
    change L (-s, -s) ≤ 0 at hb
    rw [hvec, map_smul, smul_eq_mul] at hb
    exact (not_le_of_gt (mul_pos hs hdir)) hb
  have hunbounded : ¬ Bornology.IsBounded S := by
    intro hbounded
    obtain ⟨R, hR⟩ := hbounded.exists_norm_le
    let s := max R 0 + 1
    have hs : 0 < s := by dsimp [s]; linarith [le_max_right R 0]
    have hbound := hR (-s, -s) ⟨s, hs, rfl⟩
    have hnorm : ‖((-s, -s) : ℝ × ℝ)‖ = s := by
      simp [Prod.norm_def, Real.norm_eq_abs, abs_of_pos hs]
    rw [hnorm] at hbound
    dsimp [s] at hbound
    linarith [le_max_left R 0]
  exact P.subset_outside_of_unbounded_preconnected hconn hsub hunbounded ⟨t, ht, rfl⟩

end Polygon
