import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Real.Basic

/-!
# Supporting affine hyperplanes and zero-face hulls

If an affine function is nonnegative on finitely many vertices,
its zero set in their hull is the hull of the zero vertices.
This identifies the fixed core face during Hamilton's PL
compression, pp. 67--68; see M76 derivation 86.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A point of a finite convex hull on a supporting affine zero
hyperplane lies in the hull of its zero vertices. Independence
is not required. See M76 derivation 86. -/
theorem mem_convexHull_zero_vertices (s : Finset E) (A : E →ᵃ[ℝ] ℝ)
    (hA : ∀ v ∈ s, 0 ≤ A v) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) (hAx : A x = 0) :
    x ∈ convexHull ℝ ((s : Set E) ∩ {v | A v = 0}) := by
  classical
  obtain ⟨w, hw, hsum, hval⟩ := mem_convexHull'.mp hx
  have hmap := map_affineCombination (s := s) id w hsum A
  simp only [affineCombination_eq_linear_combination _ _ _ hsum,
    id_eq, Function.comp_apply, smul_eq_mul] at hmap
  rw [hval, hAx] at hmap
  have hzero : ∀ v ∈ s, w v * A v = 0 :=
    (sum_eq_zero_iff_of_nonneg fun v hv => mul_nonneg (hw v hv) (hA v hv)).mp hmap.symm
  let t := s.filter (fun v => A v = 0)
  have ht : (t : Set E) = (s : Set E) ∩ {v | A v = 0} := by
    ext v
    simp only [t, mem_coe, mem_filter, mem_inter_iff, mem_ofPred_eq]
  have hwzero (v : E) (hvs : v ∈ s) (hvt : v ∉ t) : w v = 0 := by
    apply (mul_eq_zero.mp (hzero v hvs)).resolve_right
    intro he
    exact hvt (mem_filter.mpr ⟨hvs, he⟩)
  rw [← ht]
  apply mem_convexHull'.mpr
  refine ⟨w, fun v hv => hw v (filter_subset _ _ hv), ?_, ?_⟩
  · exact (sum_subset (filter_subset _ _) hwzero).trans hsum
  · exact (sum_subset (filter_subset _ _) (fun v hvs hvt => by
      rw [hwzero v hvs hvt, zero_smul])).trans hval

end Finset
