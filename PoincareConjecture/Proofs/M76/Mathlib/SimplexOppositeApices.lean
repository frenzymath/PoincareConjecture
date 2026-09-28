import PoincareConjecture.Proofs.M76.Mathlib.SimplexFaceCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.SimplexFacetNeighborhood
import Mathlib.Topology.Algebra.Affine

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace AffineBasis

variable {ι E : Type*} [Finite ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coord_ne_zero_of_affineSpan_update_eq_top (b : AffineBasis ι ℝ E)
    (i : ι) (q : E) (hfull : affineSpan ℝ (range (Function.update b i q)) = ⊤) :
    b.coord i q ≠ 0 := by
  intro hzero
  let S := affineSpan ℝ (b '' {j | j ≠ i})
  have hq : q ∈ S := (b.mem_affineSpan_image_iff_coord_eq_zero _ q).mpr (by
    intro j hj
    have hji : j = i := by simpa using hj
    simpa only [hji] using hzero)
  have hspan : affineSpan ℝ (range (Function.update b i q)) ≤ S := by
    apply affineSpan_le.mpr
    rintro _ ⟨j, rfl⟩
    change Function.update b i q j ∈ S
    by_cases hji : j = i
    · subst j
      rw [Function.update_self]
      exact hq
    · rw [Function.update_of_ne hji]
      exact subset_affineSpan ℝ _ (mem_image_of_mem b hji)
  have hbi : b i ∈ S := hspan (by rw [hfull]; trivial)
  have hz := b.coord_eq_zero_of_mem_affineSpan_image (s := {j | j ≠ i})
    (i := i) (by simp) hbi
  simp at hz

theorem coord_neg_of_common_facet_intersection (b : AffineBasis ι ℝ E)
    (i : ι) (q x : E) (hqi : b.coord i q ≠ 0)
    (hxi : b.coord i x = 0) (hx : ∀ j, j ≠ i → 0 < b.coord j x)
    (hinter : ∀ y ∈ convexHull ℝ (range b) ∩
      convexHull ℝ (range (Function.update b i q)), b.coord i y = 0) :
    b.coord i q < 0 := by
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ E := b.finiteDimensional
  rcases lt_or_gt_of_ne hqi with hneg | hpos
  · exact hneg
  exfalso
  let V : Set ℝ := {t | ∀ j ∈ Finset.univ.erase i,
    0 < b.coord j (AffineMap.lineMap x q t)}
  have hV : IsOpen V := by
    have he : V = ⋂ j ∈ Finset.univ.erase i,
        {t | 0 < b.coord j (AffineMap.lineMap x q t)} := by
      ext t
      simp only [V, mem_ofPred_eq, mem_iInter]
    rw [he]
    exact isOpen_biInter_finset (fun j _ => isOpen_lt continuous_const
      ((continuous_barycentric_coord b j).comp AffineMap.lineMap_continuous))
  have hzV : 0 ∈ V := by
    intro j hj
    simpa only [AffineMap.lineMap_apply_zero] using hx j (Finset.ne_of_mem_erase hj)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzV)
  let t : ℝ := min (δ / 2) (1 / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have ht1 : t ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have htV : t ∈ V := hball (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht] using htδ)
  let y := AffineMap.lineMap x q t
  have hyi : b.coord i y = t * b.coord i q := by
    change b.coord i (AffineMap.lineMap x q t) = _
    rw [AffineMap.apply_lineMap]
    simp only [hxi, AffineMap.lineMap_apply,
      vsub_eq_sub, vadd_eq_add, sub_zero, add_zero, smul_eq_mul]
  have hyold : y ∈ convexHull ℝ (range b) := by
    rw [b.convexHull_eq_nonneg_coord]
    intro j
    by_cases hji : j = i
    · subst j
      exact hyi ▸ (mul_pos ht hpos).le
    · exact (htV j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)).le
  have hxnew : x ∈ convexHull ℝ (range (Function.update b i q)) := by
    apply b.mem_convexHull_update_of_coord i q x hqi
    · simp only [hxi, zero_div, le_refl]
    · intro j hji
      simpa only [hxi, zero_div, zero_mul, sub_zero] using (hx j hji).le
  have hqnew : q ∈ convexHull ℝ (range (Function.update b i q)) :=
    subset_convexHull ℝ _ ⟨i, Function.update_self i q b⟩
  have hynew : y ∈ convexHull ℝ (range (Function.update b i q)) :=
    (convex_convexHull ℝ _).lineMap_mem hxnew hqnew ⟨ht.le, ht1⟩
  have hz := hinter y ⟨hyold, hynew⟩
  rw [hyi] at hz
  exact (mul_pos ht hpos).ne' hz

theorem mem_interior_union_of_common_facet_intersection (b : AffineBasis ι ℝ E)
    (i : ι) (q x : E) (hfull : affineSpan ℝ (range (Function.update b i q)) = ⊤)
    (hxi : b.coord i x = 0) (hx : ∀ j, j ≠ i → 0 < b.coord j x)
    (hinter : ∀ y ∈ convexHull ℝ (range b) ∩
      convexHull ℝ (range (Function.update b i q)), b.coord i y = 0) :
    x ∈ interior (convexHull ℝ (range b) ∪
      convexHull ℝ (range (Function.update b i q))) :=
  b.mem_interior_union_convexHull_update i q x
    (b.coord_neg_of_common_facet_intersection i q x
      (b.coord_ne_zero_of_affineSpan_update_eq_top i q hfull) hxi hx hinter) hxi hx

end AffineBasis
