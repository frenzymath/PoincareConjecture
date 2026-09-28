import PoincareConjecture.Proofs.M76.Mathlib.GeometricResidualTriangle
import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeLevelUniqueness

set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem zeroApexCoordinates_mem_edgeLine_iff (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hqw : q ≠ w) (hq : A q = 0) (hw : A w = 0) (hv : A v ≠ 0) (p : ℝ × ℝ) :
    A.zeroApexCoordinates q w v p ∈ affineSpan ℝ ({w, v} : Set E) ↔ p.1 = 1 := by
  have hvw : A v ≠ A w := by rwa [hw]
  constructor
  · intro hp
    have heq := A.eq_edgeLevel_of_mem_affineSpan hvw hp
      (A.apply_zeroApexCoordinates hq hw hv p)
    have hcoord := A.zeroApexCoordinates_injective hqw hq hw hv
      (heq.trans (A.zeroApexCoordinates_side q w v hw p.2).symm)
    exact congrArg Prod.fst hcoord
  · intro hp
    have hpeq : p = (1, p.2) := Prod.ext hp rfl
    rw [hpeq, A.zeroApexCoordinates_side q w v hw p.2, edgeLevel_eq_lineMap]
    exact lineMap_mem_affineSpan_pair _ w v

theorem zeroApex_residual_edgeLine_intersection (A : E →ᵃ[ℝ] ℝ) {q w v : E}
    (hqw : q ≠ w) (hq : A q = 0) (hw : A w = 0)
    {β : ℝ} (hβ : 0 < β) (hβv : β < A v) :
    convexHull ℝ (insert q ({A.edgeLevel w v β, A.edgeLevel q v β} : Set E)) ∩
        affineSpan ℝ ({w, v} : Set E) = {A.edgeLevel w v β} := by
  rw [← A.zeroApexCoordinates_residual_image hq hw hβ hβv]
  ext x
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hline⟩
    have hs := (A.zeroApexCoordinates_mem_edgeLine_iff hqw hq hw
      (hβ.trans hβv).ne' p).mp hline
    have ht : p.2 = β := le_antisymm hp.2.1.2 (by
      simpa only [hs, mul_one] using hp.2.1.1)
    have hpeq : p = (1, β) := Prod.ext hs ht
    exact mem_singleton_iff.mpr (by rw [hpeq, A.zeroApexCoordinates_side q w v hw β])
  · rintro rfl
    refine ⟨⟨(1, β), ?_, A.zeroApexCoordinates_side q w v hw β⟩, ?_⟩
    · simp [TaperedStrip.residualDomain, hβv.le]
    · rw [edgeLevel_eq_lineMap]
      exact lineMap_mem_affineSpan_pair _ w v

theorem exceptional_residual_opposite_edge_intersection (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hq : A q = 0) (hu : A u < 0) {β : ℝ} (hβ : 0 < β) (hβv : β < A v)
    (hqw : q ≠ A.zeroCrossing u v) :
    convexHull ℝ (insert q ({A.edgeLevel (A.zeroCrossing u v) v β,
        A.edgeLevel q v β} : Set E)) ∩ segment ℝ u v =
      {A.edgeLevel (A.zeroCrossing u v) v β} := by
  let w := A.zeroCrossing u v
  have hv : 0 < A v := hβ.trans hβv
  have hw : A w = 0 := A.zeroCrossing_apply (hu.trans hv).ne
  have hwseg : w ∈ segment ℝ u v :=
    openSegment_subset_segment ℝ u v (A.zeroCrossing_mem_openSegment hu hv)
  have hlines : affineSpan ℝ ({w, v} : Set E) = affineSpan ℝ ({u, v} : Set E) :=
    affineSpan_pair_eq_of_left_mem_of_ne
      (convexHull_subset_affineSpan _ (by rwa [convexHull_pair]))
      (fun h => hv.ne' (h ▸ hw))
  have hinter := A.zeroApex_residual_edgeLine_intersection hqw hq hw hβ hβv
  have hz : A.edgeLevel w v β ∈ segment ℝ u v :=
    (convex_segment u v).segment_subset hwseg (right_mem_segment ℝ u v)
      (openSegment_subset_segment ℝ w v
        (A.edgeLevel_mem_openSegment (by rw [hw]; exact hβ) hβv))
  ext x
  constructor
  · intro hx
    rw [← hinter]
    refine ⟨hx.1, ?_⟩
    rw [hlines]
    exact convexHull_subset_affineSpan _ (by simpa only [convexHull_pair] using hx.2)
  · rintro rfl
    exact ⟨(show A.edgeLevel w v β ∈
      convexHull ℝ (insert q ({A.edgeLevel w v β, A.edgeLevel q v β} : Set E)) ∩
        affineSpan ℝ ({w, v} : Set E) from hinter.symm ▸ mem_singleton _).1, hz⟩

end AffineMap
