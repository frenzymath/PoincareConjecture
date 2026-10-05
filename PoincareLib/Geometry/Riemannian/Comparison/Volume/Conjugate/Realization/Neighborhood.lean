import PoincareLib.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.ChartVariation
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Neighborhoods for chart variations

Adapted from AxelWorkspace,
`formalized-sources/riemannian/MorganTian/MorganTianLib/Geometry/SecondVariationPrep.lean`,
revision `f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e` (Apache-2.0).
Original SHA-256: e338b33769229578e2aa4aab406190705bce8a6556db3c386f96b723dc135a36.
Copyright (c) 2026 Archon Horizon. All rights reserved.
License: `references/analysis/axel-workspace/LICENSE.Apache-2.0.txt`.
Only the compact-neighborhood lemmas are retained; imports and namespace change.
-/

open Set Filter
open scoped Topology

namespace PoincareMT.Conjugate.Realization

theorem exists_forall_mem_of_isCompact_of_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : ℝ × ℝ → E} {U : Set E} {K : Set ℝ}
    (hK : IsCompact K) (hU : IsOpen U) (hcont : Continuous u)
    (hmem : ∀ t ∈ K, u (0, t) ∈ U) :
    ∃ ε > 0, ∀ s ∈ Set.Ioo (-ε) ε, ∀ t ∈ K, u (s, t) ∈ U := by
  have key : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ∀ t ∈ K, u (s, t) ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun t ht => ?_)
    have hpre : u ⁻¹' U ∈ 𝓝 ((0 : ℝ), t) := (hU.preimage hcont).mem_nhds (hmem t ht)
    filter_upwards [hpre] with z hz using hz
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨ε, hε, hkey⟩ := key
  refine ⟨ε, hε, fun s hs t ht => ?_⟩
  refine hkey ?_ t ht
  rw [Real.dist_eq, sub_zero, abs_lt]
  exact ⟨hs.1, hs.2⟩

/-- **Math.** **An open set containing a closed interval contains a thickened one.** If
`[c, d] ⊆ V` with `V` open, then `[c - ρ, d + ρ] ⊆ V` for some `ρ > 0`. Proved by taking `ρ`
half of a Mathlib thickening radius (`IsCompact.exists_thickening_subset_open`) for
`[c, d] ⊆ V`, and observing that every `x ∈ [c - ρ, d + ρ]` is within `ρ` of its clamp
`max c (min d x) ∈ [c, d]`. -/
theorem exists_Icc_enlarged_subset {V : Set ℝ} {c d : ℝ} (hV : IsOpen V) (hcd : c ≤ d)
    (hsub : Set.Icc c d ⊆ V) :
    ∃ ρ > 0, Set.Icc (c - ρ) (d + ρ) ⊆ V := by
  have hK : IsCompact (Set.Icc c d) := isCompact_Icc
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hV hsub
  refine ⟨δ / 2, by linarith, fun x hx => hthick ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  rw [Metric.mem_thickening_iff]
  refine ⟨max c (min d x), ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩, ?_⟩
  rcases lt_or_ge x c with hxc | hxc
  · have hmin : min d x = x := min_eq_right (hxc.le.trans hcd)
    have hmax : max c x = c := max_eq_left hxc.le
    rw [hmin, hmax, Real.dist_eq, abs_of_neg (by linarith : x - c < 0)]
    linarith
  · rcases le_or_gt x d with hxd | hxd
    · have hmin : min d x = x := min_eq_right hxd
      have hmax : max c x = x := max_eq_right hxc
      rw [hmin, hmax, dist_self]
      linarith
    · have hmin : min d x = d := min_eq_left hxd.le
      have hmax : max c d = d := max_eq_right hcd
      rw [hmin, hmax, Real.dist_eq, abs_of_pos (by linarith : x - d > 0)]
      linarith


end PoincareMT.Conjugate.Realization
