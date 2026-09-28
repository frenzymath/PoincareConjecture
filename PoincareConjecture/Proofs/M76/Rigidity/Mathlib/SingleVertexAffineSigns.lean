import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring










set_option autoImplicit false

open Set SignType

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]





theorem sign_eqOn_convexHull_of_single_vertex
    (a b : E →ᵃ[ℝ] ℝ) {s : Finset E} {v : E}
    (hzero : ∀ z ∈ s, z ≠ v → a z = 0 ∧ b z = 0)
    {w : E} (hw : w ∈ convexHull ℝ (s : Set E)) (hpos : 0 < a w * b w) :
    EqOn (fun x => sign (a x)) (fun x => sign (b x)) (convexHull ℝ (s : Set E)) := by
  have haw : a w ≠ 0 := (mul_ne_zero_iff.mp hpos.ne').1
  have hav : a v ≠ 0 := by
    intro hv
    have ha : EqOn a (AffineMap.const ℝ E 0) (s : Set E) := by
      intro z hz
      by_cases hzv : z = v
      · simpa only [hzv, const_apply] using hv
      · exact (hzero z hz hzv).1
    exact haw (AffineMap.eqOn_affineSpan ha (convexHull_subset_affineSpan _ hw))
  let r : ℝ := b v / a v
  have heq : EqOn b (r • a) (s : Set E) := by
    intro z hz
    change b z = r * a z
    by_cases hzv : z = v
    · rw [hzv]
      exact (div_mul_cancel₀ (b v) hav).symm
    · obtain ⟨haz, hbz⟩ := hzero z hz hzv
      rw [haz, hbz, mul_zero]
  have heqHull (x : E) (hx : x ∈ convexHull ℝ (s : Set E)) : b x = r * a x := by
    change b x = (r • a) x
    exact AffineMap.eqOn_affineSpan (f := b) (g := r • a) heq
      (convexHull_subset_affineSpan _ hx)
  have hr : 0 < r := by
    have hprod : 0 < (a w * a w) * r := by
      rw [heqHull w hw] at hpos
      convert hpos using 1
      ring
    exact (mul_pos_iff_of_pos_left (mul_self_pos.mpr haw)).mp hprod
  intro x hx
  change sign (a x) = sign (b x)
  rw [heqHull x hx, sign_mul, sign_pos hr, one_mul]

end AffineMap
