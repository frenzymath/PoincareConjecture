/-
Adapted from AxelWorkspace revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source and SHA-256: references/analysis/axel-workspace/weak-parabolic-regularity-sources.json.
Apache-2.0; see the license in that source directory.
-/
import PoincareLib.Analysis.Sobolev.WeakCompactness.DerivativeLimit
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Uniform convergence identifies a weak L2 limit

On a fixed finite-measure domain uniform convergence bounds the L2 distance
by the uniform error times the square root of the volume. Continuous linear
functionals then identify a pre-existing weak limit with this strong limit.
This is the local common-limit step toward Morgan--Tian, Chapter 18,
Lemma 18.10; it asserts no intrinsic regularized-energy lower semicontinuity.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Poincare.Analysis.Sobolev.WeakCompactness

/-- **Math.** Uniform convergence on a finite-measure set gives strong L2
convergence of the same measurable representatives. -/
theorem tendsto_toLp_of_uniformlyOn
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {mu : Measure X} {s : Set X} (hs : MeasurableSet s)
    [IsFiniteMeasure (mu.restrict s)] {f : ℕ → X → E} {v : X → E}
    (hf : ∀ n, MemLp (f n) 2 (mu.restrict s))
    (hv : MemLp v 2 (mu.restrict s)) (hlim : TendstoUniformlyOn f v atTop s) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hv.toLp v)) := by
  let a : ℝ := (measureUnivNNReal (mu.restrict s) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹
  have ha : 0 ≤ a := Real.rpow_nonneg (by positivity) _
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hd : 0 < eps / (a + 1) := div_pos heps (by linarith)
  have he := (Metric.tendstoUniformlyOn_iff.mp hlim) (eps / (a + 1)) hd
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hb : ∀ᵐ x ∂mu.restrict s,
      ‖((hf n).toLp (f n) - hv.toLp v) x‖ ≤ eps / (a + 1) := by
    filter_upwards [ae_restrict_mem hs, Lp.coeFn_sub ((hf n).toLp (f n)) (hv.toLp v),
      (hf n).coeFn_toLp, hv.coeFn_toLp] with x hx hsub hfn hvx
    rw [hsub, Pi.sub_apply, hfn, hvx]
    simpa only [dist_eq_norm, norm_sub_rev] using (hN n hn x hx).le
  calc
    _ ≤ a * (eps / (a + 1)) := Lp.norm_le_of_ae_bound hd.le hb
    _ < eps := by
      rw [← mul_div_assoc, div_lt_iff₀ (by linarith : 0 < a + 1)]
      nlinarith

/-- **Math.** A strong limit and a weak limit of one Hilbert-space sequence
coincide, by uniqueness of limits of scalar continuous linear observations. -/
theorem eq_of_strong_and_weak_limit
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : ℕ → F} {u v : F} (hs : Tendsto f atTop (𝓝 v))
    (hw : WeakConverges f u) : u = v := by
  apply ext_inner_left ℝ
  intro z
  exact tendsto_nhds_unique (hw (innerSL ℝ z))
    ((innerSL ℝ z).continuous.tendsto v |>.comp hs)

end Poincare.Analysis.Sobolev.WeakCompactness
