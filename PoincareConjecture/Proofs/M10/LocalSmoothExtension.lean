import PoincareConjecture.Proofs.M10.SupportedCalculus
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension









set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


theorem exists_compact_contDiff_two_of_germ {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    ∃ g : E → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ f =ᶠ[𝓝 x] g := by
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hf.eventually (by norm_num))
  let χ : ContDiffBump x :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  let g := fun y ↦ χ y * f y
  have hs : ContDiff ℝ 2 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact χ.contDiffAt.mul (hball (by simpa only [χ.tsupport_eq] using hy))
    · have hz : g =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
        simp only [g, hz, Pi.zero_apply, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  refine ⟨g, hs, χ.hasCompactSupport.mul_right, ?_⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  simp only [g, hy, Pi.one_apply, one_mul]

end PoincareConjecture.M10
