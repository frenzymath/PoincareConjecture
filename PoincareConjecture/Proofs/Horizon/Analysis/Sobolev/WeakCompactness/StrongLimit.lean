import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Poincare.Analysis.Sobolev.WeakCompactness

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

theorem eq_of_strong_and_weak_limit
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : ℕ → F} {u v : F} (hs : Tendsto f atTop (𝓝 v))
    (hw : WeakConverges f u) : u = v := by
  apply ext_inner_left ℝ
  intro z
  exact tendsto_nhds_unique (hw (innerSL ℝ z))
    ((innerSL ℝ z).continuous.tendsto v |>.comp hs)

end Poincare.Analysis.Sobolev.WeakCompactness
