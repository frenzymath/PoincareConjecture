import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace










set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology ENNReal SchwartzMap LineDeriv

noncomputable section

namespace PoincareConjecture.EuclideanDerivativeNative

variable {n : ℕ}

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

theorem inner_schwartzToLp (f g : 𝓢(ModelE, ℝ)) :
    inner ℝ (f.toLp 2 volume) (g.toLp 2 volume) = ∫ x, f x * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hf hg
  rw [hf, hg]
  simp [RCLike.inner_apply, mul_comm]


theorem inner_schwartzLineDeriv (φ f : 𝓢(ModelE, ℝ)) (v : ModelE) :
    inner ℝ (φ.toLp 2 volume) ((∂_{v} f).toLp 2 volume) =
      -inner ℝ ((∂_{v} φ).toLp 2 volume) (f.toLp 2 volume) := by
  rw [inner_schwartzToLp, inner_schwartzToLp]
  exact SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left φ f v


theorem schwartzLineDeriv_limit_zero (v : ModelE) (f : ℕ → 𝓢(ModelE, ℝ))
    (w : Lp ℝ 2 (volume : Measure ModelE))
    (hf : Tendsto (fun j => (f j).toLp 2 volume) atTop (𝓝 0))
    (hdf : Tendsto (fun j => (∂_{v} (f j)).toLp 2 volume) atTop (𝓝 w)) : w = 0 := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure ModelE)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  apply hdense.eq_zero_of_inner_right ℝ
  intro φ
  change inner ℝ (φ.toLp 2 volume) w = 0
  have hleft : Tendsto (fun j => inner ℝ (φ.toLp 2 volume) ((∂_{v} (f j)).toLp 2 volume))
      atTop (𝓝 (inner ℝ (φ.toLp 2 volume) w)) :=
    tendsto_const_nhds.inner hdf
  have hright : Tendsto (fun j => -inner ℝ ((∂_{v} φ).toLp 2 volume) ((f j).toLp 2 volume))
      atTop (𝓝 (-inner ℝ ((∂_{v} φ).toLp 2 volume) (0 : Lp ℝ 2 volume))) :=
    (tendsto_const_nhds.inner hf).neg
  have hright' := hright.congr' (Eventually.of_forall (fun j =>
    (inner_schwartzLineDeriv φ (f j) v).symm))
  simpa only [inner_zero_right, neg_zero] using tendsto_nhds_unique hleft hright'

end PoincareConjecture.EuclideanDerivativeNative
