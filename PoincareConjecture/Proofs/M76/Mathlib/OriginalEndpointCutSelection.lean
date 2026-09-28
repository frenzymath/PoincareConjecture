import PoincareConjecture.Proofs.M76.Mathlib.PolygonInteriorCutArcs
import Mathlib.Topology.Order.LeftRightNhds

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem exists_ordered_endpoint_cuts (P : Polygon E n)
    (U : Fin n → Set E) (hU : ∀ i, IsOpen (U i)) (hPU : ∀ i, P i ∈ U i)
    (m : Fin n → ℝ) (hm : ∀ i, m i ∈ Ioo (0 : ℝ) 1) :
    ∃ α β : Fin n → ℝ, ∀ i,
      α i ∈ Ioo 0 (m i) ∧ β i ∈ Ioo (m i) 1 ∧
      P.edgeCut α i ∈ U i ∧ P.edgeCut β i ∈ U (finRotate n i) ∧
      segment ℝ (P.edgeCut α i) (P.edgeCut β i) =
        AffineMap.lineMap (P i) (P (finRotate n i)) '' Icc (α i) (β i) ∧
      P.edgeCut m i ∈ segment ℝ (P.edgeCut α i) (P.edgeCut β i) ∧
      segment ℝ (P.edgeCut α i) (P.edgeCut β i) ⊆
        AffineMap.lineMap (P i) (P (finRotate n i)) '' Ioo (0 : ℝ) 1 := by
  have hleft (i : Fin n) : ∃ a ∈ Ioo 0 (m i),
      AffineMap.lineMap (P i) (P (finRotate n i)) a ∈ U i := by
    have hnear : ∀ᶠ r : ℝ in 𝓝[>] 0,
        AffineMap.lineMap (P i) (P (finRotate n i)) r ∈ U i :=
      AffineMap.lineMap_continuous.continuousWithinAt.eventually_mem
        (by simpa only [AffineMap.lineMap_apply_zero] using (hU i).mem_nhds (hPU i))
    obtain ⟨a, haU, ha⟩ := (hnear.and (Ioo_mem_nhdsGT (hm i).1)).exists
    exact ⟨a, ha, haU⟩
  have hright (i : Fin n) : ∃ b ∈ Ioo (m i) 1,
      AffineMap.lineMap (P i) (P (finRotate n i)) b ∈ U (finRotate n i) := by
    have hnear : ∀ᶠ r : ℝ in 𝓝[<] 1,
        AffineMap.lineMap (P i) (P (finRotate n i)) r ∈ U (finRotate n i) :=
      AffineMap.lineMap_continuous.continuousWithinAt.eventually_mem
        (by simpa only [AffineMap.lineMap_apply_one] using
          (hU (finRotate n i)).mem_nhds (hPU (finRotate n i)))
    obtain ⟨b, hbU, hb⟩ := (hnear.and (Ioo_mem_nhdsLT (hm i).2)).exists
    exact ⟨b, hb, hbU⟩
  choose α hα hαU using hleft
  choose β hβ hβU using hright
  refine ⟨α, β, fun i => ?_⟩
  have heq : segment ℝ (P.edgeCut α i) (P.edgeCut β i) =
      AffineMap.lineMap (P i) (P (finRotate n i)) '' Icc (α i) (β i) := by
    change segment ℝ (AffineMap.lineMap _ _ (α i)) (AffineMap.lineMap _ _ (β i)) = _
    rw [← image_segment ℝ, segment_eq_Icc ((hα i).2.trans (hβ i).1).le]
  refine ⟨hα i, hβ i, hαU i, hβU i, heq, ?_, ?_⟩
  · rw [heq]
    exact mem_image_of_mem _ ⟨(hα i).2.le, (hβ i).1.le⟩
  · rw [heq]
    apply image_mono
    intro r hr
    exact ⟨(hα i).1.trans_le hr.1, hr.2.trans_lt (hβ i).2⟩

end Polygon
