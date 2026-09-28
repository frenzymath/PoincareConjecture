import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.LineLevel
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Ring











set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane



noncomputable def bendGraph (u v : ℝ × ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then (u.2 / u.1) * t else (v.2 / v.1) * t



theorem continuous_bendGraph (u v : ℝ × ℝ) : Continuous (bendGraph u v) := by
  exact (continuous_const.mul continuous_id).if_le (continuous_const.mul continuous_id)
    continuous_id continuous_const (fun t ht => by simp [ht])



theorem lineLevelPoint_fst_zero {v : ℝ × ℝ} (hv : v.1 ≠ 0) (t : ℝ) :
    lineLevelPoint (LinearMap.fst ℝ ℝ ℝ) 0 v t = (t, (v.2 / v.1) * t) := by
  change AffineMap.lineMap (0 : ℝ × ℝ) v ((t - 0) / (v.1 - 0)) = _
  simp only [sub_zero, AffineMap.lineMap_apply_module', add_zero]
  apply Prod.ext
  · exact div_mul_cancel₀ t hv
  · change t / v.1 * v.2 = v.2 / v.1 * t
    ring



theorem mem_segment_zero_iff_graph {v z : ℝ × ℝ} (hv : v.1 ≠ 0) :
    z ∈ segment ℝ 0 v ↔ z.1 ∈ uIcc 0 v.1 ∧ z.2 = (v.2 / v.1) * z.1 := by
  have hfst : (LinearMap.fst ℝ ℝ ℝ) (0 : ℝ × ℝ) ≠ (LinearMap.fst ℝ ℝ ℝ) v :=
    hv.symm
  have hlevel := lineLevelPoint_mem_segment_iff (LinearMap.fst ℝ ℝ ℝ) hfst z.1
  constructor
  · intro hz
    have hrec := lineLevelPoint_eq_of_mem_segment (LinearMap.fst ℝ ℝ ℝ) hfst hz
    refine ⟨hlevel.mp (hrec.symm ▸ hz), ?_⟩
    have hy := congrArg Prod.snd hrec
    simpa only [lineLevelPoint_fst_zero hv, LinearMap.fst_apply] using hy.symm
  · rintro ⟨hz, hy⟩
    have he : lineLevelPoint (LinearMap.fst ℝ ℝ ℝ) 0 v z.1 = z := by
      rw [lineLevelPoint_fst_zero hv]
      exact Prod.ext rfl hy.symm
    rw [← he]
    exact hlevel.mpr hz



theorem mem_two_segments_zero_iff_graph {u v z : ℝ × ℝ} (hu : u.1 < 0) (hv : 0 < v.1) :
    z ∈ segment ℝ 0 u ∪ segment ℝ 0 v ↔
      u.1 ≤ z.1 ∧ z.1 ≤ v.1 ∧ z.2 = bendGraph u v z.1 := by
  rw [mem_union, mem_segment_zero_iff_graph hu.ne, mem_segment_zero_iff_graph hv.ne',
    uIcc_of_ge hu.le, uIcc_of_le hv.le]
  by_cases hz : z.1 ≤ 0
  · rw [bendGraph, if_pos hz]
    constructor
    · rintro (⟨hzu, hy⟩ | ⟨hzv, hy⟩)
      · exact ⟨hzu.1, hz.trans hv.le, hy⟩
      · have hz0 : z.1 = 0 := le_antisymm hz hzv.1
        exact ⟨hu.le.trans hzv.1, hzv.2, by simpa only [hz0, mul_zero] using hy⟩
    · rintro ⟨hzu, _, hy⟩
      exact Or.inl ⟨⟨hzu, hz⟩, hy⟩
  · rw [bendGraph, if_neg hz]
    constructor
    · rintro (⟨hzu, _⟩ | ⟨hzv, hy⟩)
      · exact False.elim (hz hzu.2)
      · exact ⟨hu.le.trans hzv.1, hzv.2, hy⟩
    · rintro ⟨_, hzv, hy⟩
      exact Or.inr ⟨⟨(lt_of_not_ge hz).le, hzv⟩, hy⟩



theorem exists_open_two_segments_graph {u v : ℝ × ℝ} (hu : u.1 < 0) (hv : 0 < v.1) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0 : ℝ × ℝ) ∈ U ∧
      ∀ z ∈ U, z ∈ segment ℝ 0 u ∪ segment ℝ 0 v ↔ z.2 = bendGraph u v z.1 := by
  refine ⟨Prod.fst ⁻¹' Ioo u.1 v.1, isOpen_Ioo.preimage continuous_fst, ⟨hu, hv⟩, ?_⟩
  intro z hz
  rw [mem_two_segments_zero_iff_graph hu hv]
  exact ⟨fun h => h.2.2, fun h => ⟨hz.1.le, hz.2.le, h⟩⟩

end Poincare.Manifold.Schoenflies.Plane
