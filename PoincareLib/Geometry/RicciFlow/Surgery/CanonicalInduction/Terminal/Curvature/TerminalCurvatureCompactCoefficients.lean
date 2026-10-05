import PoincareLib.Geometry.Riemannian.Coordinates.CompactEnergy
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Curvature.TerminalCurvatureUniformScalar

/-!
# Uniform source metric bounds on a fixed compact chart

The same compact-uniform coefficient jets retain a positive quadratic
floor and all requested finite bounds before the source index.
Source: derivations/terminal-curvature-compact-charts.md, Stage J1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilinear" => E →L[ℝ] E →L[ℝ] ℝ

/-- A compact positive coefficient field has one finite jet bound and
one quadratic floor throughout the actual coordinate buffer. -/
theorem terminalCurvature_compact_coefficient_bounds
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {B : E → Bilinear} (hB : ContDiffOn ℝ ∞ B U)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v) (m : ℕ) :
    ∃ b : ℝ, 0 < b ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K,
      ‖x‖ ≤ C ∧ (∀ j ≤ m, ‖iteratedFDeriv ℝ j B x‖ ≤ C) ∧
      ∀ v : E, b * ‖v‖ ^ 2 ≤ B x v v := by
  classical
  obtain ⟨b, hb, hlow⟩ := exists_uniform_bilinear_lower_bound hK
    (hB.continuousOn.mono hKU) hpos
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  have hfinite (j : Fin (m + 1)) : ∃ C : ℝ,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ (j : ℕ) B x‖ ≤ C :=
    hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hB hU
        (by exact_mod_cast le_top)).mono hKU)
  choose C hC using hfinite
  obtain ⟨C1, hC1⟩ := Finite.exists_le C
  refine ⟨b, hb, max 1 (max C0 C1), le_max_left _ _, ?_⟩
  intro x hx
  refine ⟨(hC0 x hx).trans ((le_max_left _ _).trans (le_max_right _ _)), ?_,
    hlow x hx⟩
  intro j hj
  exact ((hC ⟨j, by omega⟩ x hx).trans (hC1 ⟨j, by omega⟩)).trans
    ((le_max_right _ _).trans (le_max_right _ _))

/-- Actual uniform finite jet convergence keeps a common positive
quadratic floor, coordinate bound and source coefficient bound. -/
theorem terminalCurvature_eventually_compact_coefficient_bounds
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {B0 : E → Bilinear} (hB0 : ContDiffOn ℝ ∞ B0 U)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B0 x v v)
    {B : ℕ → E → Bilinear} (m : ℕ)
    (hjet : ∀ j ≤ m, TendstoUniformlyOn (fun k => iteratedFDeriv ℝ j (B k))
      (iteratedFDeriv ℝ j B0) atTop K) :
    ∃ b : ℝ, 0 < b ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
      ‖x‖ ≤ C ∧ (∀ j ≤ m, ‖iteratedFDeriv ℝ j (B k) x‖ ≤ C) ∧
      ∀ v : E, b * ‖v‖ ^ 2 ≤ B k x v v := by
  obtain ⟨b, hb, C, hC, hbound⟩ :=
    terminalCurvature_compact_coefficient_bounds hU hK hKU hB0 hpos m
  let eta := min 1 (b / 2)
  have heta : 0 < eta := lt_min zero_lt_one (half_pos hb)
  have htail : ∀ᶠ k in atTop, ∀ j : Fin (m + 1), ∀ x ∈ K,
      ‖iteratedFDeriv ℝ (j : ℕ) (B k) x - iteratedFDeriv ℝ (j : ℕ) B0 x‖ ≤ eta := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hjet j (by omega))) eta heta]
      with k hk x hx
    have hh := hk x hx
    rw [dist_comm, dist_eq_norm] at hh
    exact hh.le
  refine ⟨b / 2, half_pos hb, C + 1, by linarith, ?_⟩
  filter_upwards [htail] with k hk x hx
  obtain ⟨hcoord, hjets, hlow⟩ := hbound x hx
  refine ⟨hcoord.trans (by linarith), ?_, ?_⟩
  · intro j hj
    have hdiff := hk ⟨j, by omega⟩ x hx
    have htri := norm_le_norm_sub_add (iteratedFDeriv ℝ j (B k) x)
      (iteratedFDeriv ℝ j B0 x)
    have he1 : eta ≤ 1 := min_le_left _ _
    linarith [hjets j hj]
  · intro v
    have hzero := hk ⟨0, by omega⟩ x hx
    have hdiff : ‖B k x - B0 x‖ ≤ eta := by
      have heq : iteratedFDeriv ℝ 0 (B k) x - iteratedFDeriv ℝ 0 B0 x =
          iteratedFDeriv ℝ 0 (fun y => B k y - B0 y) x := by
        ext v
        rfl
      rw [heq, norm_iteratedFDeriv_zero] at hzero
      exact hzero
    have he : ‖(B k x - B0 x) v v‖ ≤ eta * ‖v‖ ^ 2 := by
      calc
        _ ≤ ‖(B k x - B0 x) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖B k x - B0 x‖ * ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ (eta * ‖v‖) * ‖v‖ := by gcongr
        _ = _ := by ring
    have hlower := neg_le_of_abs_le (show |B k x v v - B0 x v v| ≤
      eta * ‖v‖ ^ 2 by simpa only [sub_apply, Real.norm_eq_abs] using he)
    have hsmall := mul_le_mul_of_nonneg_right
      (show eta ≤ b / 2 from min_le_right _ _) (sq_nonneg ‖v‖)
    nlinarith [hlow v]

end PoincareMT.M47
