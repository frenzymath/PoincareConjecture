import PoincareConjecture.Proofs.M76.Mathlib.TaperedTriangleEdgeIncidence
import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalTriangleSlice
import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeSlab










set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem exists_exceptional_triangle_tapered_collar (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hi : AffineIndependent ℝ ![q, u, v]) (hq : A q = 0)
    (hu : A u < 0) (hv : 0 < A v) {β : ℝ} (hβ : 0 < β) (hβv : β < A v) :
    ∃ H : TaperedStrip.domain β ≃ₜ
        convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)),
      H.IsFinitePL ∧
        (∀ p, (H p : E) = A.zeroApexCoordinates q (A.zeroCrossing u v) v p) ∧
        (∀ p, A (H p) = (p : ℝ × ℝ).2) ∧
        (convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)) ⊆
          convexHull ℝ (insert q ({u, v} : Set E))) ∧
        (convexHull ℝ (insert q ({u, v} : Set E)) ∩ {x | A x = 0} =
          segment ℝ q (A.zeroCrossing u v)) ∧
        (∀ p, (H p : E) ∈ segment ℝ u v ↔ (p : ℝ × ℝ).1 = 1) ∧
        (∀ p, (H p : E) ∈ segment ℝ q u ↔ (p : ℝ × ℝ) = (0, 0)) ∧
        ∀ p, (H p : E) ∈ segment ℝ q v ↔ (p : ℝ × ℝ) = (0, 0) := by
  let w := A.zeroCrossing u v
  have hw : A w = 0 := A.zeroCrossing_apply (hu.trans hv).ne
  have hwseg : w ∈ segment ℝ u v :=
    openSegment_subset_segment ℝ u v (A.zeroCrossing_mem_openSegment hu hv)
  have hwspan : w ∈ affineSpan ℝ ({u, v} : Set E) :=
    convexHull_subset_affineSpan _ (by rwa [convexHull_pair])
  have hqnot : q ∉ affineSpan ℝ ({u, v} : Set E) := by
    intro h
    have hset : (![q, u, v] : Fin 3 → E) '' ({1, 2} : Set (Fin 3)) = {u, v} := by
      rw [image_insert_eq, image_singleton]
      rfl
    have hmem : (0 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) :=
      (hi.mem_affineSpan_iff (0 : Fin 3) ({1, 2} : Set (Fin 3))).mp
        (by rw [hset]; exact h)
    exact (by decide : (0 : Fin 3) ∉ ({1, 2} : Set (Fin 3))) hmem
  have hqw : q ≠ w := fun h => hqnot (by rw [h]; exact hwspan)
  have hwv : w ≠ v := by
    intro h
    exact hv.ne' (h ▸ hw)
  have hlines : affineSpan ℝ ({w, v} : Set E) = affineSpan ℝ ({u, v} : Set E) :=
    affineSpan_pair_eq_of_left_mem_of_ne hwspan hwv
  obtain ⟨H, hH, hval, hheight⟩ := A.exists_zeroApex_tapered_collar hqw hq hw hv.ne' hβ
  have hsmall := A.zeroApex_collar_subset_triangle q hw hv hβ hβv.le
  have hlarge : convexHull ℝ (insert q ({w, v} : Set E)) ⊆
      convexHull ℝ (insert q ({u, v} : Set E)) := by
    apply convexHull_min ?_ (convex_convexHull ℝ _)
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact subset_convexHull ℝ _ (by simp)
    · exact convexHull_mono (subset_insert q ({u, v} : Set E))
        (by rwa [convexHull_pair])
    · exact subset_convexHull ℝ _ (by simp)
  refine ⟨H, hH, hval, hheight, hsmall.trans hlarge,
    A.convexHull_zero_apex_pair_inter_zero hq hu hv, ?_, ?_, ?_⟩
  · intro p
    rw [hval]
    constructor
    · intro hm
      have hspan : A.zeroApexCoordinates q w v p ∈ affineSpan ℝ ({w, v} : Set E) := by
        rw [hlines]
        exact convexHull_subset_affineSpan _ (by rwa [convexHull_pair])
      have hvw : A v ≠ A w := by rw [hw]; exact hv.ne'
      have hpoint := A.eq_edgeLevel_of_mem_affineSpan hvw hspan
        (A.apply_zeroApexCoordinates hq hw hv.ne' p)
      have hparam := A.zeroApexCoordinates_injective hqw hq hw hv.ne'
        (hpoint.trans (A.zeroApexCoordinates_side q w v hw (p : ℝ × ℝ).2).symm)
      exact congrArg Prod.fst hparam
    · intro hp
      have hm := (A.zeroApexCoordinates_mem_side_iff hqw hq hw hv hβv.le p.property).mpr hp
      exact (convex_segment u v).segment_subset hwseg (right_mem_segment ℝ u v) hm
  · intro p
    constructor
    · intro hm
      have hnonpos : segment ℝ q u ⊆ {x | A x ≤ 0} := by
        rw [← convexHull_pair]
        apply convexHull_min ?_ ((convex_Iic (0 : ℝ)).affine_preimage A)
        intro x hx
        rcases hx with rfl | rfl
        · exact hq.le
        · exact hu.le
      have ht : (p : ℝ × ℝ).2 = 0 := by
        have hle : A (H p) ≤ 0 := hnonpos hm
        rw [hheight] at hle
        exact le_antisymm hle p.property.2.1
      have hqu : A u ≠ A q := by rw [hq]; exact hu.ne
      have heq : (H p : E) = q := A.injOn_edgeLine hqu
        (convexHull_subset_affineSpan _ (by rwa [convexHull_pair]))
        (left_mem_affineSpan_pair ℝ q u) ((hheight p).trans (ht.trans hq.symm))
      have hzero : A.zeroApexCoordinates q w v (0, 0) = q := by
        rw [zeroApexCoordinates_bottom, lineMap_apply_zero]
      exact A.zeroApexCoordinates_injective hqw hq hw hv.ne'
        ((hval p).symm.trans (heq.trans hzero.symm))
    · intro hp
      rw [hval, hp, zeroApexCoordinates_bottom, lineMap_apply_zero]
      exact left_mem_segment ℝ q u
  · intro p
    rw [hval]
    exact A.zeroApexCoordinates_mem_far_edge_iff hqw hq hw hv hβv p.property

end AffineMap
