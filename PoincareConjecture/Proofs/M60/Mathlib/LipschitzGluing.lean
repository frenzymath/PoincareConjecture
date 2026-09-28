import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.EMetricSpace.Lipschitz










set_option autoImplicit false

open Set Metric
open scoped Convex NNReal ENNReal

attribute [local instance] Classical.propDecidable

namespace PoincareConjecture.M60




theorem lipschitzOnWith_piecewise_of_convex
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoEMetricSpace Y]
    {S : Set E} (hS : Convex ℝ S) (φ : E → ℝ) (hφ : ContinuousOn φ S) (r : ℝ)
    {f h : E → Y} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f (S ∩ {x | φ x ≤ r}))
    (hh : LipschitzOnWith L h (S ∩ {x | r ≤ φ x}))
    (heq : ∀ x ∈ S, φ x = r → f x = h x) :
    LipschitzOnWith (max K L) ({x | φ x ≤ r}.piecewise f h) S := by
  have hcross {x y : E} (hx : x ∈ S) (hy : y ∈ S)
      (hxr : φ x ≤ r) (hyr : r ≤ φ y) :
      edist (f x) (h y) ≤ (↑(max K L) : ℝ≥0∞) * edist x y := by
    obtain ⟨z, hz, hzr⟩ := (convex_segment x y).isPreconnected.intermediate_value
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
      (hφ.mono (hS.segment_subset hx hy)) ⟨hxr, hyr⟩
    have hzS : z ∈ S := hS.segment_subset hx hy hz
    have hdist : edist x z + edist z y = edist x y := by
      simp only [edist_dist]
      rw [← ENNReal.ofReal_add dist_nonneg dist_nonneg, dist_add_dist_of_mem_segment hz]
    calc
      edist (f x) (h y) ≤ edist (f x) (f z) + edist (f z) (h y) := edist_triangle _ _ _
      _ = edist (f x) (f z) + edist (h z) (h y) := by rw [heq z hzS hzr]
      _ ≤ K * edist x z + L * edist z y :=
        add_le_add (hf ⟨hx, hxr⟩ ⟨hzS, hzr.le⟩) (hh ⟨hzS, hzr.ge⟩ ⟨hy, hyr⟩)
      _ ≤ (↑(max K L) : ℝ≥0∞) * edist x z + (↑(max K L) : ℝ≥0∞) * edist z y := by
        gcongr
        · exact_mod_cast le_max_left K L
        · exact_mod_cast le_max_right K L
      _ = (↑(max K L) : ℝ≥0∞) * edist x y := by rw [← mul_add, hdist]
  intro x hx y hy
  by_cases hxr : φ x ≤ r <;> by_cases hyr : φ y ≤ r
  · simp only [piecewise, mem_ofPred_eq, if_pos hxr, if_pos hyr]
    apply (hf ⟨hx, hxr⟩ ⟨hy, hyr⟩).trans
    gcongr
    exact_mod_cast le_max_left K L
  · simp only [piecewise, mem_ofPred_eq, if_pos hxr, if_neg hyr]
    exact hcross hx hy hxr (le_of_not_ge hyr)
  · simp only [piecewise, mem_ofPred_eq, if_neg hxr, if_pos hyr]
    simpa only [edist_comm] using hcross hy hx hyr (le_of_not_ge hxr)
  · simp only [piecewise, mem_ofPred_eq, if_neg hxr, if_neg hyr]
    apply (hh ⟨hx, le_of_not_ge hxr⟩ ⟨hy, le_of_not_ge hyr⟩).trans
    gcongr
    exact_mod_cast le_max_right K L

end PoincareConjecture.M60
