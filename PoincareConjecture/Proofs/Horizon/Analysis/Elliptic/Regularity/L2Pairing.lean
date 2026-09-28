import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Poincare.Analysis.Elliptic

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

theorem inner_toLp_eq_integral_mul {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

theorem tendsto_integral_mul_of_eLpNorm_sub {l : Filter ι}
    {f g : α → ℝ} {v : ι → α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (hlim : Tendsto (fun i => eLpNorm (v i - g) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, f x * v i x ∂μ) l (𝓝 (∫ x, f x * g x ∂μ)) := by
  have hv' := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv g hg).mpr hlim
  have hi := (tendsto_const_nhds (x := hf.toLp f)).inner (𝕜 := ℝ) hv'
  simpa only [inner_toLp_eq_integral_mul] using hi

end Poincare.Analysis.Elliptic
