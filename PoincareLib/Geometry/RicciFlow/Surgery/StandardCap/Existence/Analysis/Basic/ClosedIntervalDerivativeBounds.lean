import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Derivative bounds through continuous interval endpoints

The interior mean-value estimate extends to the closed interval by
continuity. Applied to the fixed-coordinate metric jets, this gives
uniform control of their initial values in Morgan-Tian Theorem 12.5,
p. 297; see fixed-chart-endpoint.md.
-/

set_option autoImplicit false

open Set

/-- An interior derivative bound controls differences at both included
endpoints (Theorem 12.5, p. 297, endpoint calculus). -/
theorem norm_sub_le_of_interior_deriv_bound_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ C)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖f t - f s‖ ≤ C * |t - s| := by
  have hl : LipschitzOnWith ⟨C, hC⟩ f (Ioo a b) :=
    (convex_Ioo a b).lipschitzOnWith_of_nnnorm_deriv_le hd (fun t ht => hb t ht)
  have hc : ContinuousOn f (closure (Ioo a b)) := by rwa [closure_Ioo hab.ne]
  have hclosed : LipschitzOnWith ⟨C, hC⟩ f (Icc a b) := by
    simpa only [closure_Ioo hab.ne] using LipschitzOnWith.closure hc hl
  convert! hclosed.dist_le_mul t ht s hs using 1
  simp only [dist_eq_norm]
