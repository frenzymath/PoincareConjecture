import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Polygons.TriangleEdgeSection










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "W3" => ((ℝ × ℝ) × ℝ)

private theorem exists_lineMap_pos_mem {y v : V3} {U : Set V3}
    (hU : IsOpen U) (hy : y ∈ U) :
    ∃ t ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap y v t ∈ U := by
  have hopen : IsOpen ((AffineMap.lineMap y v : ℝ → V3) ⁻¹' U) :=
    hU.preimage (lipschitzWith_lineMap y v).continuous
  have hzero : (0 : ℝ) ∈ (AffineMap.lineMap y v : ℝ → V3) ⁻¹' U := by
    simpa only [mem_preimage, AffineMap.lineMap_apply_zero] using hy
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let t := min (delta / 2) (1 / 2)
  have ht : 0 < t := lt_min (half_pos hdelta) (by norm_num)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨t, ⟨ht, ht1⟩, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
  exact (min_le_left _ _).trans_lt (half_lt_self hdelta)



theorem edge_chart_height_nonzero
    (F : W3 ≃ᴬ[ℝ] V3) {p q y : V3} {V : Set V3}
    (hF : F 0 = y) (hV : IsOpen V) (hyV : y ∈ V)
    (hy : y ∈ openSegment ℝ p q) (hpq : p ≠ q)
    (haxis : ∀ x ∈ V, x ∈ segment ℝ p q → (F.symm x).1 = 0) :
    (F.symm p).2 ≠ 0 ∧ (F.symm q).2 ≠ 0 := by
  have hy0 : F.symm y = 0 := by rw [← hF, F.symm_apply_apply]
  have hyp : y ≠ p := by
    intro h
    exact hpq (left_mem_openSegment_iff.mp (h ▸ hy))
  have hyq : y ≠ q := by
    intro h
    exact hpq (right_mem_openSegment_iff.mp (h ▸ hy))
  have each (v : V3) (hv : v ∈ segment ℝ p q) (hyv : y ≠ v) :
      (F.symm v).2 ≠ 0 := by
    intro hvzero
    obtain ⟨t, ht, htV⟩ := exists_lineMap_pos_mem (v := v) hV hyV
    let z := AffineMap.lineMap y v t
    have hzseg : z ∈ segment ℝ p q :=
      (convex_segment p q).segment_subset (openSegment_subset_segment ℝ p q hy) hv
        (lineMap_mem_segment ℝ y v ⟨ht.1.le, ht.2.le⟩)
    have hzfirst : (F.symm z).1 = 0 := haxis z htV hzseg
    have hzsnd : (F.symm z).2 = 0 := by
      change (F.symm.toAffineEquiv.toAffineMap (AffineMap.lineMap y v t)).2 = 0
      rw [AffineMap.apply_lineMap]
      change (AffineMap.lineMap (F.symm y) (F.symm v) t).2 = 0
      rw [hy0]
      simp [AffineMap.lineMap_apply_module, hvzero]
    have hzy : z = y := by
      apply F.symm.injective
      rw [hy0]
      exact Prod.ext hzfirst hzsnd
    have htzero := AffineMap.lineMap_injective ℝ hyv
      (hzy.trans (AffineMap.lineMap_apply_zero y v).symm)
    exact ht.1.ne' htzero
  exact ⟨each p (left_mem_segment ℝ p q) hyp, each q (right_mem_segment ℝ p q) hyq⟩



theorem edge_chart_triangle_halfInterval
    (F : W3 ≃ᴬ[ℝ] V3) {p q w y : V3} {V : Set V3}
    (hF : F 0 = y) (hV : IsOpen V) (hyV : y ∈ V)
    (hy : y ∈ openSegment ℝ p q) (hpq : p ≠ q)
    (haxis : ∀ x ∈ V, x ∈ segment ℝ p q → (F.symm x).1 = 0)
    (hw : w ∉ affineSpan ℝ ({p, q} : Set V3)) :
    ∃ (z : V3) (r : ℝ), z ≠ y ∧ 0 < r ∧ r < dist y z ∧ Metric.ball y r ⊆ V ∧
      (convexHull ℝ (insert w ({p, q} : Set V3)) ∩ {x | (F.symm x).2 = 0}) ∩
          Metric.ball y r = AffineMap.lineMap y z '' Ico (0 : ℝ) (r / dist y z) ∧
      Topology.IsEmbedding (AffineMap.lineMap y z : ℝ → V3) ∧
      ∀ t ∈ Ico (0 : ℝ) (r / dist y z),
        AffineMap.lineMap y z t ∈ segment ℝ p q ↔ t = 0 := by
  let A : V3 →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap.comp
    F.symm.toAffineEquiv.toAffineMap
  have hyzero : A y = 0 := by
    change (F.symm y).2 = 0
    rw [← hF, F.symm_apply_apply]
    rfl
  have hends := edge_chart_height_nonzero F hF hV hyV hy hpq haxis
  change A p ≠ 0 ∧ A q ≠ 0 at hends
  have hA (x : V3) : A x = (F.symm x).2 := rfl
  obtain ⟨t, ht, hty⟩ := (openSegment_eq_image_lineMap ℝ p q).symm ▸ hy
  have hcomb : (1 - t) * A p + t * A q = 0 := by
    rw [← hty, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring] at hyzero
    exact hyzero
  have hopposite : (A p < 0 ∧ 0 < A q) ∨ (A q < 0 ∧ 0 < A p) := by
    rcases lt_or_gt_of_ne hends.1 with hp | hp
    · left
      refine ⟨hp, ?_⟩
      by_contra! hq
      have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr ht.2) hp
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos ht.1.le hq
      linarith
    · right
      refine ⟨?_, hp⟩
      by_contra! hq
      have hpos := mul_pos (sub_pos.mpr ht.2) hp
      have hnonneg := mul_nonneg ht.1.le hq
      linarith
  have hyl : y ∈ affineSpan ℝ ({p, q} : Set V3) := by
    apply convexHull_subset_affineSpan
    rw [convexHull_pair]
    exact openSegment_subset_segment ℝ p q hy
  rcases hopposite with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · have hyeq := A.eq_zeroCrossing_of_mem_affineSpan (hp.trans hq).ne hyl hyzero
    simpa only [← hyeq, hA] using A.exists_triangle_edge_halfInterval hp hq hw hV (hyeq ▸ hyV)
  · have hyl' : y ∈ affineSpan ℝ ({q, p} : Set V3) := by rwa [pair_comm]
    have hyeq := A.eq_zeroCrossing_of_mem_affineSpan (hq.trans hp).ne hyl' hyzero
    have hw' : w ∉ affineSpan ℝ ({q, p} : Set V3) := by rwa [pair_comm]
    simpa only [← hyeq, hA, pair_comm q p, segment_symm ℝ q p] using
      A.exists_triangle_edge_halfInterval hq hp hw' hV (hyeq ▸ hyV)

end PoincareConjecture.M76
