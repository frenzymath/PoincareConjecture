import PoincareConjecture.Proofs.M25.Topology3D.Plane.CornerSectors
import PoincareConjecture.Proofs.M25.Topology3D.Plane.UnitTriangle
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

theorem exists_openSegment_mem_unitCorner {a b : ℝ × ℝ}
    (ha : min a.1 a.2 < 0) (hb : 0 < b.1 ∧ 0 < b.2)
    (haH : a.1 + a.2 < 1) (hbH : b.1 + b.2 < 1) :
    ∃ w ∈ openSegment ℝ a b, w ∈ unitCorner ∧ w.1 + w.2 < 1 := by
  let g : ℝ → ℝ := fun t =>
    min (AffineMap.lineMap a b t).1 (AffineMap.lineMap a b t).2
  have hline : Continuous (AffineMap.lineMap a b : ℝ → ℝ × ℝ) :=
    AffineMap.lineMap_continuous
  have hg : Continuous g := hline.fst.min hline.snd
  have hg0 : g 0 < 0 := by simpa only [g, AffineMap.lineMap_apply_zero] using ha
  have hg1 : 0 < g 1 := by
    simpa only [g, AffineMap.lineMap_apply_one, lt_min_iff] using hb
  obtain ⟨t, ht, ht0⟩ := intermediate_value_Ioo (show (0 : ℝ) ≤ 1 by norm_num)
    hg.continuousOn ⟨hg0, hg1⟩
  let w := AffineMap.lineMap a b t
  have hw : w ∈ openSegment ℝ a b := lineMap_mem_openSegment ℝ a b ht
  have hw0 : min w.1 w.2 = 0 := ht0
  have hnonneg : 0 ≤ w.1 ∧ 0 ≤ w.2 := le_min_iff.mp (by rw [hw0])
  have hhalf : Convex ℝ {x : ℝ × ℝ | x.1 + x.2 < 1} :=
    (convex_Iio (𝕜 := ℝ) 1).linear_preimage
      (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ)
  have hwH : w.1 + w.2 < 1 := hhalf.openSegment_subset haH hbH hw
  refine ⟨w, hw, ?_, hwH⟩
  apply (mem_unitCorner_iff w).mpr
  rcases min_eq_iff.mp hw0 with ⟨hx, _⟩ | ⟨hy, _⟩
  · exact Or.inr ⟨hx, hnonneg.2, by linarith⟩
  · exact Or.inl ⟨hnonneg.1, by linarith, hy⟩

theorem exists_endpoint_interior_unitTriangle_le_sum {a b z : ℝ × ℝ}
    (hz : z ∈ segment ℝ a b) (hzT : z ∈ interior unitTriangle)
    (havoid : segment ℝ a b ∩ unitCorner ⊆ {(1, 0), (0, 1)}) :
    ∃ c ∈ ({a, b} : Set (ℝ × ℝ)), c ∈ interior unitTriangle ∧
      c.1 + c.2 ≤ z.1 + z.2 := by
  rw [interior_unitTriangle] at hzT
  let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ
  have hmin : min (L a) (L b) ≤ L z :=
    ((convex_Ici (𝕜 := ℝ) (min (L a) (L b))).linear_preimage L).segment_subset
      (show min (L a) (L b) ≤ L a from min_le_left _ _)
      (show min (L a) (L b) ≤ L b from min_le_right _ _) hz
  obtain ⟨c, hc, hcH⟩ : ∃ c ∈ ({a, b} : Set (ℝ × ℝ)), L c ≤ L z := by
    rcases le_total (L a) (L b) with hab | hba
    · exact ⟨a, Or.inl rfl, by simpa only [min_eq_left hab] using hmin⟩
    · exact ⟨b, Or.inr rfl, by simpa only [min_eq_right hba] using hmin⟩
  change c.1 + c.2 ≤ z.1 + z.2 at hcH
  have hcseg : c ∈ segment ℝ a b := by
    rcases hc with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hcHlt : c.1 + c.2 < 1 := hcH.trans_lt hzT.2.2
  have hcornerSum (w : ℝ × ℝ) (hw : w ∈ segment ℝ a b) (hwC : w ∈ unitCorner) :
      w.1 + w.2 = 1 := by
    rcases havoid ⟨hw, hwC⟩ with rfl | rfl <;> norm_num
  have hcT : c ∈ unitTriangle := by
    by_contra hcT
    have hneg : min c.1 c.2 < 0 := by
      apply lt_of_not_ge
      intro hge
      have hnn := le_min_iff.mp hge
      exact hcT ⟨hnn.1, hnn.2, hcHlt.le⟩
    obtain ⟨w, hw, hwC, hwH⟩ := exists_openSegment_mem_unitCorner hneg
      ⟨hzT.1, hzT.2.1⟩ hcHlt hzT.2.2
    have hwseg : w ∈ segment ℝ a b :=
      (convex_segment (𝕜 := ℝ) a b).openSegment_subset hcseg hz hw
    exact hwH.ne (hcornerSum w hwseg hwC)
  have hcC : c ∉ unitCorner := fun h => hcHlt.ne (hcornerSum c hcseg h)
  have hcx : 0 < c.1 := by
    by_contra! h
    have heq : c.1 = 0 := le_antisymm h hcT.1
    exact hcC ((mem_unitCorner_iff c).mpr (Or.inr ⟨heq, hcT.2.1, by linarith⟩))
  have hcy : 0 < c.2 := by
    by_contra! h
    have heq : c.2 = 0 := le_antisymm h hcT.2.1
    exact hcC ((mem_unitCorner_iff c).mpr (Or.inl ⟨hcT.1, by linarith, heq⟩))
  refine ⟨c, hc, ?_, hcH⟩
  rw [interior_unitTriangle]
  exact ⟨hcx, hcy, hcHlt⟩

end PoincareConjecture.M25.Topology3D
