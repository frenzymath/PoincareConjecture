import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Basic









noncomputable section
set_option autoImplicit false

open Set InnerProductGeometry

universe u v

namespace Poincare.Euclidean

theorem exists_card_le_of_unit_angle_separated
    (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {α : ℝ} (hα : 0 < α) :
    ∃ N : ℕ, ∀ {ι : Type v} [Fintype ι] (v : ι → V),
      (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → α ≤ angle (v i) (v j)) → Fintype.card ι ≤ N := by
  classical
  let β := min α Real.pi
  have hβ : 0 < β := lt_min hα Real.pi_pos
  have hβπ : β ≤ Real.pi := min_le_right _ _
  have hcos : Real.cos β < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by rfl) hβπ hβ
  let δ := Real.sqrt (2 - 2 * Real.cos β)
  have hδ : 0 < δ := Real.sqrt_pos.2 (by linarith)
  have hδsq : δ ^ 2 = 2 - 2 * Real.cos β := Real.sq_sqrt (by linarith)
  have hsep {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
      (hxy : α ≤ angle x y) : δ ≤ dist x y := by
    have hc : Real.cos (angle x y) ≤ Real.cos β :=
      Real.cos_le_cos_of_nonneg_of_le_pi hβ.le (angle_le_pi _ _)
        ((min_le_left _ _).trans hxy)
    have hd := norm_sub_pow_two_real x y
    rw [hx, hy, inner_eq_cos_angle_of_norm_eq_one hx hy] at hd
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x - y)]
  obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_sphere (0 : V) 1).totallyBounded (δ / 2) (by positivity)
  let := hs.fintype
  refine ⟨Fintype.card s, ?_⟩
  intro ι _ v hv hangle
  have hchoice (i : ι) : ∃ z : s, dist (v i) z < δ / 2 := by
    have hi : v i ∈ Metric.sphere (0 : V) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hv i
    obtain ⟨z, hz, hiz⟩ := Set.mem_iUnion₂.mp (hcover hi)
    exact ⟨⟨z, hz⟩, hiz⟩
  choose z hz using hchoice
  apply Fintype.card_le_of_injective z
  intro i j hij
  by_contra hne
  have hlower := hsep (hv i) (hv j) (hangle i j hne)
  have hupper := dist_triangle (v i) (z i : V) (v j)
  have hj := hz j
  rw [← hij, dist_comm] at hj
  linarith [hz i]

end Poincare.Euclidean
