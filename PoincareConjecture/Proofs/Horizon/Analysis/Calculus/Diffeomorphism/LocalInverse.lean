import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Ring.Units










noncomputable section
set_option autoImplicit false

open Filter Set
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem eventually_contDiffAt_localInverse
    {f : E → F} {x : E} (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ f y)
    (e : E ≃L[ℝ] F) (hd : HasFDerivAt f (e : E →L[ℝ] F) x) :
    ∀ᶠ z in 𝓝 (f x),
      ContDiffAt ℝ ∞ (hf.self_of_nhds.localInverse hd (by simp)) z := by
  let G := hf.self_of_nhds.toOpenPartialHomeomorph f hd (by simp)
  have hx : x ∈ G.source := hf.self_of_nhds.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hc : ContinuousAt (fun y => (e.symm : F →L[ℝ] E).comp (fderiv ℝ f y)) x :=
    continuousAt_const.clm_comp (hf.self_of_nhds.continuousAt_fderiv (by simp))
  have hu : IsUnit ((e.symm : F →L[ℝ] E).comp (fderiv ℝ f x)) := by
    rw [hd.fderiv]
    have he : (e.symm : F →L[ℝ] E).comp (e : E →L[ℝ] F) = 1 := by
      ext v
      simp [ContinuousLinearMap.one_def]
    rw [he]
    exact isUnit_one
  have hnear : ∀ᶠ y in 𝓝 x, (fderiv ℝ f y).IsInvertible := by
    filter_upwards [hc.eventually (Units.isOpen.mem_nhds hu)] with y hy
    have hunit : ((e.symm : F →L[ℝ] E).comp (fderiv ℝ f y)).IsInvertible :=
      ⟨ContinuousLinearEquiv.ofUnit hy.unit, hy.unit_spec⟩
    exact ContinuousLinearMap.isInvertible_equiv_comp.mp hunit
  have hmaps : Tendsto G.symm (𝓝 (f x)) (𝓝 x) := G.tendsto_symm hx
  filter_upwards [hmaps.eventually hf, hmaps.eventually hnear,
    G.open_target.mem_nhds (G.map_source hx)] with z hz hi hzt
  obtain ⟨a, ha⟩ := hi
  have hd' : HasFDerivAt f (a : E →L[ℝ] F) (G.symm z) := by
    rw [ha]
    exact (hz.differentiableAt (by simp)).hasFDerivAt
  exact G.contDiffAt_symm hzt hd' hz

end Poincare.Analysis.Calculus
