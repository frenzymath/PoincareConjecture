import PoincareConjecture.Proofs.M76.Mathlib.ProjectiveHalfspace










set_option autoImplicit false

open Set
open scoped BigOperators

namespace LinearMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]



theorem fractionalRadial_denom_pos_convexHull (L : E →ₗ[ℝ] ℝ)
    {s : Set E} (hs : ∀ x ∈ s, 0 < 1 + L x) :
    ∀ x ∈ convexHull ℝ s, 0 < 1 + L x :=
  convexHull_min hs ((convex_Ioi (0 : ℝ)).affine_preimage
    (AffineMap.const ℝ E 1 + L.toAffineMap))

private theorem fractionalRadial_image_convexHull_subset (L : E →ₗ[ℝ] ℝ)
    {s : Set E} (hs : ∀ x ∈ s, 0 < 1 + L x) :
    L.fractionalRadial '' convexHull ℝ s ⊆ convexHull ℝ (L.fractionalRadial '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  have hdx := L.fractionalRadial_denom_pos_convexHull hs x hx
  obtain ⟨ι, _, w, z, hw, hwSum, hz, rfl⟩ := mem_convexHull_iff_exists_fintype.mp hx
  let d := 1 + L (∑ i, w i • z i)
  have hd : 0 < d := hdx
  have hdSum : (∑ i, w i * (1 + L (z i))) = d := by
    simp only [d, mul_add, mul_one, Finset.sum_add_distrib, hwSum,
      map_sum, map_smul, smul_eq_mul]
  apply mem_convexHull_of_exists_fintype
    (fun i => w i * (1 + L (z i)) / d) (fun i => L.fractionalRadial (z i))
  · intro i
    exact div_nonneg (mul_nonneg (hw i) (hs (z i) (hz i)).le) hd.le
  · simp only [div_eq_mul_inv, ← Finset.sum_mul, hdSum, mul_inv_cancel₀ hd.ne']
  · intro i
    exact mem_image_of_mem _ (hz i)
  · change (∑ i, (w i * (1 + L (z i)) / d) • L.fractionalRadial (z i)) =
      d⁻¹ • (∑ i, w i • z i)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [fractionalRadial, smul_smul, smul_smul]
    congr 1
    field_simp [(hs (z i) (hz i)).ne', hd.ne']




theorem fractionalRadial_image_convexHull (L : E →ₗ[ℝ] ℝ)
    {s : Set E} (hs : ∀ x ∈ s, 0 < 1 + L x) :
    L.fractionalRadial '' convexHull ℝ s = convexHull ℝ (L.fractionalRadial '' s) := by
  apply Subset.antisymm (L.fractionalRadial_image_convexHull_subset hs)
  have hneg : ∀ y ∈ L.fractionalRadial '' s, 0 < 1 + (-L) y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [L.fractionalRadial_neg_denom (hs x hx).ne']
    exact inv_pos.mpr (hs x hx)
  have himage : (-L).fractionalRadial '' (L.fractionalRadial '' s) = s := by
    rw [image_image]
    exact image_congr (fun x hx => L.fractionalRadial_neg_apply (hs x hx).ne') |>.trans
      (image_id s)
  intro y hy
  have hx := (-L).fractionalRadial_image_convexHull_subset hneg
    (mem_image_of_mem (-L).fractionalRadial hy)
  rw [himage] at hx
  refine ⟨(-L).fractionalRadial y, hx, ?_⟩
  have hd := (-L).fractionalRadial_denom_pos_convexHull hneg y hy
  simpa only [neg_neg] using (-L).fractionalRadial_neg_apply hd.ne'

end LinearMap
