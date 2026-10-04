import PoincareLib.Geometry.Riemannian.Coordinates.CompactFamily

/-!
# Bilinear convergence relative to a distinct positive reference form

Morgan--Tian Claim 11.34, printed pp. 288-289, and Claim 11.35, p. 290,
use convergence of curvature tensors on compact sets. The reference energy
below is a positive metric family even when the limiting tensor is Ricci.
The argument uses the eligible M07
`exists_uniform_bilinear_family_lower_bound` and the actual bilinear
operator norm. Reviewed derivation:
`claim11_34-slice-curvature-comparison.md`, section 1.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u v w

namespace PoincareMT.M32

/-- Uniform bilinear convergence gives one relative quadratic error bound
for all vectors over a compact set, with a separate positive reference
form. Source: Claim 11.34, pp. 288-289, and Claim 11.35, p. 290;
`claim11_34-slice-curvature-comparison.md`, section 1. -/
theorem eventually_bilinear_quadratic_error_le
    {X : Type u} {E : Type v} {I : Type w}
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set X} (hK : IsCompact K) {l : Filter I}
    {g : X → E →L[ℝ] E →L[ℝ] ℝ}
    {A : I → X → E →L[ℝ] E →L[ℝ] ℝ}
    {B : X → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContinuousOn g K)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hconv : TendstoUniformlyOn A B l K) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ i in l, ∀ x ∈ K, ∀ v : E,
      |A i x v v - B x v v| ≤ epsilon * g x v v := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_family_lower_bound hK hg hpos
  filter_upwards [(Metric.tendstoUniformlyOn_iff
    (α := E →L[ℝ] E →L[ℝ] ℝ)).mp hconv (epsilon * c) (mul_pos hepsilon hc)]
    with i hi x hx v
  have hd : ‖A i x - B x‖ < epsilon * c := by
    simpa only [dist_eq_norm, norm_sub_rev] using hi x hx
  have hb := (A i x - B x).le_opNorm₂ v v
  calc
    |A i x v v - B x v v| ≤ ‖A i x - B x‖ * ‖v‖ ^ 2 := by
      simpa only [sub_apply, Real.norm_eq_abs, pow_two, mul_assoc] using hb
    _ ≤ (epsilon * c) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hd.le (sq_nonneg ‖v‖)
    _ = epsilon * (c * ‖v‖ ^ 2) := by ring
    _ ≤ epsilon * g x v v := mul_le_mul_of_nonneg_left (hbound x hx v) hepsilon.le

end PoincareMT.M32
