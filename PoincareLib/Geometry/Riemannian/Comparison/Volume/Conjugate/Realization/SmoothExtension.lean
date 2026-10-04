import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Poincaré Ch. 1 — extending locally-smooth curve data to all of `ℝ`

Adapted from AxelWorkspace,
`formalized-sources/riemannian/MorganTian/MorganTianLib/Foundations/SmoothExtension.lean`,
revision `f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e` (Apache-2.0).
Original SHA-256: 8a3d0a1f5c41c4d659e628d27a3a31ebe38ad69721023c7fcecb00d783502a63.
License: `references/analysis/axel-workspace/LICENSE.Apache-2.0.txt`.
The namespace is adapted to the current realization modules.

The broken-variation machinery of `prop:minimal-geodesic-no-conjugate` is stated
for data that is `ContDiff` on **all** of `ℝ`: `PoincareMT.Conjugate.Realization.contDiff_chartVariation`
wants `ContDiff ℝ n ŷ`, `ContDiff ℝ n Ŷ`, `ContDiff ℝ n ĉ₀`, `ContDiff ℝ n ĉ₁`, and
`PoincareMT.Conjugate.Realization.deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand` wants
`ContDiff ℝ 3 u` on the whole parameter plane.

The actual data is never global: the chart reading of a geodesic is smooth only
where the geodesic stays in the chart source
(`PoincareMT.Conjugate.Realization.contDiffOn_chartReading_of_isGeodesicOn`), which is an open interval,
not `ℝ`.  This file closes that gap once, for one-variable data, with the standard
bump cut-off:

* `exists_contDiff_eqOn_of_contDiffOn_Ioo` — if `f` is `C^n` on `Ioo a b` and
  `[c, d] ⊆ (a, b)`, there is a **globally** `C^n` function `F` agreeing with `f`
  on an **open neighbourhood** `V` of `[c, d]` with `V ⊆ (a, b)`.

The neighbourhood, not merely `[c, d]` itself, is the point: the consumers
differentiate the data, and `fderiv`/`deriv` at a point only see a neighbourhood,
so `EqOn F f (Icc c d)` alone would be useless (it would not give
`deriv F = deriv f` even at interior points, let alone at `c` and `d`).

*Construction.*  Let `m = (c + d)/2` and `h = (d − c)/2`, so `[c, d]` is the closed
ball `closedBall m h`.  Take `ε = min (c − a) (b − d) > 0` and the `ContDiffBump`
at `m` with `rIn = h + ε/3` and `rOut = h + 2ε/3`.  It is `1` on `closedBall m rIn
⊇ [c, d]`, and its topological support is `closedBall m rOut ⊆ (a, b)`.  Put
`F = χ · f` on `(a, b)` and `F = 0` elsewhere.  On the open set `(a, b)` this is
`χ · f`, which is `C^n`; on the open set `(tsupport χ)ᶜ` it is identically `0`; and
these two open sets cover `ℝ` precisely because `tsupport χ ⊆ (a, b)`.  Finally `F`
agrees with `f` on the open ball `V = ball m rIn ∋ [c, d]`, where `χ = 1`.

Blueprint: `prop:minimal-geodesic-no-conjugate`.
-/

open Set Metric

noncomputable section

namespace PoincareMT.Conjugate.Realization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Math.** **Locally-smooth curve data extends to globally-smooth curve data.**
If `f : ℝ → E` is `C^n` on the open interval `(a, b)` and `[c, d] ⊆ (a, b)`, then
there are a globally `C^n` function `F : ℝ → E` and an **open** set `V` with
`[c, d] ⊆ V ⊆ (a, b)` on which `F` and `f` agree.

Because `V` is open, every derivative of `F` on `V` — of any order, and in
particular the ones the second-variation machinery takes — coincides with the
corresponding derivative of `f`.  So a result proved for the global `F` transfers
verbatim to the local `f` on `[c, d]`.

This is what lets the genuinely-local chart data of a geodesic (smooth only where
the geodesic stays in one chart) be fed to `PoincareMT.Conjugate.Realization.chartVariation` and to
`PoincareMT.Conjugate.Realization.deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`, both of
which demand `ContDiff` on all of `ℝ`. -/
theorem exists_contDiff_eqOn_of_contDiffOn_Ioo {f : ℝ → E} {a b c d : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f (Ioo a b)) (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ∃ (F : ℝ → E) (V : Set ℝ),
      ContDiff ℝ n F ∧ IsOpen V ∧ Icc c d ⊆ V ∧ V ⊆ Ioo a b ∧ EqOn F f V := by
  classical
  set m : ℝ := (c + d) / 2 with hm
  set h : ℝ := (d - c) / 2 with hh
  have hh0 : 0 ≤ h := by simp only [hh]; linarith
  set ε : ℝ := min (c - a) (b - d) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  -- the cut-off: `1` on `closedBall m (h + ε/3)`, supported in `closedBall m (h + 2ε/3)`
  set χ : ContDiffBump m :=
    { rIn := h + ε / 3
      rOut := h + 2 * ε / 3
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith } with hχ
  have hrIn : χ.rIn = h + ε / 3 := rfl
  have hrOut : χ.rOut = h + 2 * ε / 3 := rfl
  -- `[c, d]` sits inside the open ball where `χ = 1`
  have hIccV : Icc c d ⊆ ball m χ.rIn := by
    intro x hx
    rw [Real.ball_eq_Ioo, hrIn]
    have : m - h = c ∧ m + h = d := by constructor <;> · simp only [hm, hh]; ring
    obtain ⟨hL, hR⟩ := this
    constructor
    · have := hx.1; linarith [hL ▸ (le_refl (m - h))]
    · have := hx.2; linarith [hR ▸ (le_refl (m + h))]
  -- the support of `χ` sits inside `(a, b)`
  have htsup : tsupport (χ : ℝ → ℝ) ⊆ Ioo a b := by
    rw [χ.tsupport_eq, Real.closedBall_eq_Icc, hrOut]
    intro x hx
    have hεa : ε ≤ c - a := min_le_left _ _
    have hεb : ε ≤ b - d := min_le_right _ _
    have hL : m - h = c := by simp only [hm, hh]; ring
    have hR : m + h = d := by simp only [hm, hh]; ring
    constructor
    · have := hx.1; nlinarith [hL]
    · have := hx.2; nlinarith [hR]
  have hVab : ball m χ.rIn ⊆ Ioo a b :=
    (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (le_of_lt χ.rIn_lt_rOut))).trans
      (χ.tsupport_eq ▸ htsup)
  -- the extension
  refine ⟨fun x => if x ∈ Ioo a b then χ x • f x else 0, ball m χ.rIn, ?_,
    isOpen_ball, hIccV, hVab, ?_⟩
  · -- `C^n`: the two open sets `Ioo a b` and `(tsupport χ)ᶜ` cover `ℝ`
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ioo a b
    · -- near `x` the function is `χ • f`, which is `C^n` on the open set `Ioo a b`
      have heq : (fun y => if y ∈ Ioo a b then χ y • f y else 0)
          =ᶠ[nhds x] fun y => χ y • f y := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        simp [hy]
      exact (((χ.contDiff (n := n)).contDiffOn.smul hf).contDiffAt
        (isOpen_Ioo.mem_nhds hx)).congr_of_eventuallyEq heq
    · -- `x` is outside `Ioo a b`, hence outside `tsupport χ`, where the function is `0`
      have hxts : x ∉ tsupport (χ : ℝ → ℝ) := fun hc => hx (htsup hc)
      have heq : (fun y => if y ∈ Ioo a b then χ y • f y else 0)
          =ᶠ[nhds x] fun _ => (0 : E) := by
        filter_upwards [(isClosed_tsupport (χ : ℝ → ℝ)).isOpen_compl.mem_nhds hxts]
          with y hy
        by_cases hy' : y ∈ Ioo a b
        · have : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
          simp [hy', this]
        · simp [hy']
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · -- on the inner ball `χ = 1`, so the extension is `f`
    intro x hx
    have hxab : x ∈ Ioo a b := hVab hx
    have hχ1 : χ x = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hx)
    simp [hxab, hχ1]

end PoincareMT.Conjugate.Realization

end
