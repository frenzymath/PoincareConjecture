import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Total manifold derivatives in a fixed target chart

Morgan-Tian Definition 18.17, printed p. 430. Nonsmooth area is measured
using the coordinate derivative and the inverse chart's pullback metric.
The chain-rule identity holds for total derivatives as well: a continuous
map is differentiable exactly when its expression in a smooth chart is.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold Topology

namespace PoincareMT.M60

/-- Express the total derivative of a continuous map in one fixed
smooth target chart, including nondifferentiable points. Source:
MT Definition 18.17, p. 430, nonsmooth-area measurability derivation. -/
theorem mfderiv_eq_inverse_chart_comp_fderiv
    {E F G H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {I : ModelWithCorners ℝ G H} [TopologicalSpace M] [ChartedSpace H M]
    (e : OpenPartialHomeomorph M F) (he : e.MDifferentiable I 𝓘(ℝ, F))
    {f : E → M} {z : E} (hf : ContinuousAt f z) (hz : f z ∈ e.source) :
    mfderiv 𝓘(ℝ, E) I f z =
      (mfderiv 𝓘(ℝ, F) I e.symm (e (f z))).comp (fderiv ℝ (e ∘ f) z) := by
  have hlocal : e.symm ∘ (e ∘ f) =ᶠ[𝓝 z] f := by
    filter_upwards [hf.preimage_mem_nhds (e.open_source.mem_nhds hz)] with y hy
    exact e.left_inv hy
  have hi := he.mdifferentiableAt_symm (e.map_source hz)
  by_cases hd : MDifferentiableAt 𝓘(ℝ, E) I f z
  · have hc := (he.mdifferentiableAt hz).comp z hd
    calc
      mfderiv 𝓘(ℝ, E) I f z = mfderiv 𝓘(ℝ, E) I (e.symm ∘ (e ∘ f)) z :=
        hlocal.mfderiv_eq.symm
      _ = (mfderiv 𝓘(ℝ, F) I e.symm (e (f z))).comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (e ∘ f) z) := mfderiv_comp z hi hc
      _ = _ := by rw [mfderiv_eq_fderiv]
  · have hc : ¬DifferentiableAt ℝ (e ∘ f) z := by
      intro hc
      exact hd ((hi.comp z hc.mdifferentiableAt).congr_of_eventuallyEq hlocal.symm)
    rw [mfderiv_zero_of_not_mdifferentiableAt hd, fderiv_zero_of_not_differentiableAt hc,
      ContinuousLinearMap.comp_zero]

end PoincareMT.M60
