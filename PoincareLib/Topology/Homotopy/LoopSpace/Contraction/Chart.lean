import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Convex.Basic

/-!
# Smooth interpolation in one manifold chart

This is the chartwise building block for the contraction in Morgan--Tian
Lemma 18.27, printed p. 434. The permitted chart replacement is described in
Mapher's `proof-work/tasks/M58/derivations/2026-09-19-local-chart-contraction.md`.
It makes no global choice of a chart or a uniform contraction radius.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.LoopSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]

/-- Affine interpolation from q to p in the chart at c. Endpoint and
regularity lemmas retain chart membership hypotheses. Source: the chart
replacement for MT Lemma 18.27, p. 434, in the local-contraction derivation. -/
noncomputable def chartContraction (c : M) (v : ℝ × (M × M)) : M :=
  (extChartAt I c).symm
    ((1 - v.1) • extChartAt I c v.2.2 + v.1 • extChartAt I c v.2.1)

/-- The interpolation starts at its second point. Source: the chart
replacement for MT Lemma 18.27, printed p. 434. -/
theorem chartContraction_zero (c p q : M) (hq : q ∈ (extChartAt I c).source) :
    chartContraction I c (0, p, q) = q := by
  simpa [chartContraction] using (extChartAt I c).left_inv hq

/-- The interpolation ends at its first point. Source: the chart
replacement for MT Lemma 18.27, printed p. 434. -/
theorem chartContraction_one (c p q : M) (hp : p ∈ (extChartAt I c).source) :
    chartContraction I c (1, p, q) = p := by
  simpa [chartContraction] using (extChartAt I c).left_inv hp

/-- Chart interpolation fixes the diagonal for every real time. Source:
the constant-fixing contraction of MT Lemma 18.27, printed p. 434. -/
theorem chartContraction_diagonal (c p : M) (hp : p ∈ (extChartAt I c).source)
    (t : ℝ) : chartContraction I c (t, p, p) = p := by
  simp only [chartContraction, ← add_smul, sub_add_cancel, one_smul]
  exact (extChartAt I c).left_inv hp

/-- Coordinates of the interpolation are the affine segment whenever that
segment lies in the chart target. Source: MT Lemma 18.27, p. 434, chart replacement. -/
theorem extChartAt_chartContraction (c : M) (v : ℝ × (M × M))
    (hv : (1 - v.1) • extChartAt I c v.2.2 + v.1 • extChartAt I c v.2.1 ∈
      (extChartAt I c).target) :
    extChartAt I c (chartContraction I c v) =
      (1 - v.1) • extChartAt I c v.2.2 + v.1 • extChartAt I c v.2.1 :=
  (extChartAt I c).right_inv hv

/-- Interpolation remains in any convex coordinate neighborhood of both
points. Source: the chart replacement for MT Lemma 18.27, p. 434. -/
theorem chartContraction_mem_convex (c p q : M) {V : Set E}
    (hV : Convex ℝ V) (hsub : V ⊆ (extChartAt I c).target)
    (hp : extChartAt I c p ∈ V) (hq : extChartAt I c q ∈ V)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    chartContraction I c (t, p, q) ∈ (extChartAt I c).source ∧
      extChartAt I c (chartContraction I c (t, p, q)) ∈ V := by
  have hv : (1 - t) • extChartAt I c q + t • extChartAt I c p ∈ V :=
    hV hq hp (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  exact ⟨(extChartAt I c).map_target (hsub hv),
    (extChartAt_chartContraction I c (t, p, q) (hsub hv)) ▸ hv⟩

variable [I.Boundaryless] [IsManifold I ∞ M]

/-- Joint smoothness of the chart interpolation on its actual domain.
Source: the smooth local contraction used in MT Lemma 18.27, p. 434,
implemented with charts in the local-contraction derivation. -/
theorem contMDiffAt_chartContraction (c : M) (v : ℝ × (M × M))
    (hp : v.2.1 ∈ (extChartAt I c).source)
    (hq : v.2.2 ∈ (extChartAt I c).source)
    (hv : (1 - v.1) • extChartAt I c v.2.2 + v.1 • extChartAt I c v.2.1 ∈
      (extChartAt I c).target) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) I ∞ (chartContraction I c) v := by
  have hp' : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) 𝓘(ℝ, E) ∞
      (fun w : ℝ × (M × M) => extChartAt I c w.2.1) v :=
    (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hp)).comp v
      (contMDiffAt_fst.comp v contMDiffAt_snd)
  have hq' : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) 𝓘(ℝ, E) ∞
      (fun w : ℝ × (M × M) => extChartAt I c w.2.2) v :=
    (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hq)).comp v
      (contMDiffAt_snd.comp v contMDiffAt_snd)
  have hcoord : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) 𝓘(ℝ, E) ∞
      (fun w : ℝ × (M × M) =>
        (1 - w.1) • extChartAt I c w.2.2 + w.1 • extChartAt I c w.2.1) v :=
    ((contMDiffAt_const.sub contMDiffAt_fst).smul hq').add (contMDiffAt_fst.smul hp')
  exact ((contMDiffOn_extChartAt_symm c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hv)).comp v hcoord

/-- In particular the interpolation is smooth near every time and every
diagonal point in the chart. Source: the chart replacement for
MT Lemma 18.27, printed p. 434. -/
theorem contMDiffAt_chartContraction_diagonal (c p : M)
    (hp : p ∈ (extChartAt I c).source) (t : ℝ) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) I ∞ (chartContraction I c) (t, p, p) := by
  apply contMDiffAt_chartContraction I c (t, p, p) hp hp
  simp only [← add_smul, sub_add_cancel, one_smul]
  exact (extChartAt I c).map_source hp

end PoincareMT.LoopSpace
