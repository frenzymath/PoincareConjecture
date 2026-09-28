import PoincareConjecture.Proofs.M76.Mathlib.TriangleZeroSlice
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def heightRay (A : E →ᵃ[ℝ] ℝ) (v u : E) : E :=
  (A u - A v)⁻¹ • (u - v)

theorem linear_heightRay (A : E →ᵃ[ℝ] ℝ) {v u : E} (h : A u ≠ A v) :
    A.linear (A.heightRay v u) = 1 := by
  have hsub : A.linear (u - v) = A u - A v := A.linearMap_vsub u v
  rw [heightRay, map_smul, hsub]
  change (A u - A v)⁻¹ * (A u - A v) = 1
  exact inv_mul_cancel₀ (sub_ne_zero.mpr h)

noncomputable def edgeLevel (A : E →ᵃ[ℝ] ℝ) (v u : E) (c : ℝ) : E :=
  (c - A v) • A.heightRay v u + v

theorem edgeLevel_eq_lineMap (A : E →ᵃ[ℝ] ℝ) (v u : E) (c : ℝ) :
    A.edgeLevel v u c = lineMap v u ((c - A v) / (A u - A v)) := by
  simp only [edgeLevel, heightRay, lineMap_apply_module', div_eq_mul_inv, mul_smul]

theorem apply_edgeLevel (A : E →ᵃ[ℝ] ℝ) {v u : E} (h : A u ≠ A v) (c : ℝ) :
    A (A.edgeLevel v u c) = c := by
  change A ((c - A v) • A.heightRay v u +ᵥ v) = c
  rw [map_vadd, map_smul, linear_heightRay A h]
  change (c - A v) * 1 + A v = c
  ring

theorem edgeLevel_mem_openSegment (A : E →ᵃ[ℝ] ℝ) {v u : E} {c : ℝ}
    (hv : A v < c) (hu : c < A u) : A.edgeLevel v u c ∈ openSegment ℝ v u := by
  rw [edgeLevel_eq_lineMap]
  apply lineMap_mem_openSegment
  have hgap : 0 < A u - A v := sub_pos.mpr (hv.trans hu)
  exact ⟨div_pos (sub_pos.mpr hv) hgap, (div_lt_one hgap).mpr (by linarith)⟩

theorem triangle_section_eq_edgeLevels (A : E →ᵃ[ℝ] ℝ) {v u w : E} {c : ℝ}
    (hv : A v < c) (hu : c < A u) (hw : c < A w) :
    convexHull ℝ (insert v ({u, w} : Set E)) ∩ {x | A x = c} =
      segment ℝ (A.edgeLevel v u c) (A.edgeLevel v w c) := by
  let B : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E c - A
  have hBu : B u < 0 := sub_neg.mpr hu
  have hBw : B w < 0 := sub_neg.mpr hw
  have hBv : 0 < B v := sub_pos.mpr hv
  have heq (z : E) (hz : c < A z) : A.edgeLevel v z c = B.zeroCrossing z v := by
    apply B.eq_zeroCrossing_of_mem_affineSpan (ne_of_lt ((sub_neg.mpr hz).trans hBv))
    · rw [edgeLevel_eq_lineMap, Set.pair_comm]
      exact lineMap_mem_affineSpan_pair _ v z
    · change c - A (A.edgeLevel v z c) = 0
      rw [apply_edgeLevel A (ne_of_gt (hv.trans hz)), sub_self]
  rw [heq u hu, heq w hw]
  convert B.convexHull_insert_pair_inter_zero hBu hBw hBv using 2
  ext x
  change A x = c ↔ c - A x = 0
  exact eq_comm.trans sub_eq_zero.symm

theorem heightRay_ne_of_affineIndependent (A : E →ᵃ[ℝ] ℝ) {v u w : E}
    (hi : AffineIndependent ℝ ![v, u, w]) (hu : A u ≠ A v) :
    A.heightRay v u ≠ A.heightRay v w := by
  have hlin := (affineIndependent_iff_linearIndependent_vsub ℝ ![v, u, w] 0).mp hi
  let i : {j : Fin 3 // j ≠ 0} := ⟨1, by decide⟩
  let j : {j : Fin 3 // j ≠ 0} := ⟨2, by decide⟩
  intro h
  have hij := hlin.eq_of_smul_apply_eq_smul_apply
    (A u - A v)⁻¹ (A w - A v)⁻¹ i j (inv_ne_zero (sub_ne_zero.mpr hu)) h
  have : (1 : Fin 3) = 2 := congrArg Subtype.val hij
  exact (by decide : (1 : Fin 3) ≠ 2) this

end AffineMap
