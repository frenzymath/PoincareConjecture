import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Geometry.Manifold.Diffeomorph








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]



theorem map_nhds_eq_of_contMDiffAt_bijective_mfderiv_modelSpaces
    {f : M → N} {x : M} (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x)
    (hbij : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    map f (𝓝 x) = 𝓝 (f x) := by
  let c := extChartAt 𝓘(ℝ, E) x
  let d := extChartAt 𝓘(ℝ, F) (f x)
  let A := writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x f
  have hA : ContDiffAt ℝ 1 A (c x) := by
    simpa [A, c, writtenInExtChartAt, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))).2
  have hderiv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x = fderiv ℝ A (c x) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [A, c]
  have hAbij : Function.Bijective (fderiv ℝ A (c x)) := by rwa [hderiv] at hbij
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ A (c x))
    (LinearMap.ker_eq_bot.mpr hAbij.1) (LinearMap.range_eq_top.mpr hAbij.2)
  have hstrict : HasStrictFDerivAt A (L : E →L[ℝ] F) (c x) :=
    hA.hasStrictFDerivAt' (hA.differentiableAt (by norm_num)).hasFDerivAt (by norm_num)
  have hcmap : map c.symm (𝓝 (c x)) = 𝓝 x := by
    simpa [c] using map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℝ, E)) x
  have hdmap : map d.symm (𝓝 (d (f x))) = 𝓝 (f x) := by
    simpa [d] using map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℝ, F)) (f x)
  have hfc : Tendsto (f ∘ c.symm) (𝓝 (c x)) (𝓝 (f x)) :=
    hf.continuousAt.tendsto.comp hcmap.le
  have heq : d.symm ∘ A =ᶠ[𝓝 (c x)] f ∘ c.symm := by
    filter_upwards [hfc.eventually
      ((isOpen_extChartAt_source (I := 𝓘(ℝ, F)) (f x)).mem_nhds
        (mem_extChartAt_source (I := 𝓘(ℝ, F)) (f x)))] with y hy
    exact d.left_inv hy
  have hAx : A (c x) = d (f x) := by simp [A, c, d, writtenInExtChartAt]
  calc
    map f (𝓝 x) = map (f ∘ c.symm) (𝓝 (c x)) := by rw [← map_map, hcmap]
    _ = map (d.symm ∘ A) (𝓝 (c x)) := map_congr heq.symm
    _ = map d.symm (map A (𝓝 (c x))) := (map_map ..).symm
    _ = map d.symm (𝓝 (A (c x))) := by rw [hstrict.map_nhds_eq_of_equiv]
    _ = 𝓝 (f x) := by rw [hAx, hdmap]

variable [IsManifold 𝓘(ℝ, E) ∞ M]



theorem contMDiffAt_of_local_left_inverse_modelSpaces
    {f : M → N} {g : N → M} {x : M}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x)
    (hbij : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))
    (hleft : ∀ᶠ z in 𝓝 x, g (f z) = z) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ g (f x) := by
  let c := extChartAt 𝓘(ℝ, E) x
  let d := extChartAt 𝓘(ℝ, F) (f x)
  let A := writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) x f
  have hA : ContDiffAt ℝ ∞ A (c x) := by
    simpa [A, c, writtenInExtChartAt, contDiffWithinAt_univ] using (contMDiffAt_iff.mp hf).2
  have hderiv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x = fderiv ℝ A (c x) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [A, c]
  have hAbij : Function.Bijective (fderiv ℝ A (c x)) := by rwa [hderiv] at hbij
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ A (c x))
    (LinearMap.ker_eq_bot.mpr hAbij.1) (LinearMap.range_eq_top.mpr hAbij.2)
  have hdA : HasFDerivAt A (L : E →L[ℝ] F) (c x) :=
    (hA.differentiableAt (by simp)).hasFDerivAt
  let i := hA.localInverse hdA (by simp)
  have hi : ContDiffAt ℝ ∞ i (A (c x)) := hA.to_localInverse hdA (by simp)
  have hix : i (A (c x)) = c x := hA.localInverse_apply_image hdA (by simp)
  have hAx : A (c x) = d (f x) := by simp [A, c, d, writtenInExtChartAt]
  have hil : ∀ᶠ z in 𝓝 (c x), i (A z) = z :=
    (hA.hasStrictFDerivAt' hdA (by simp)).eventually_left_inverse
  have hc : ContinuousAt c x := continuousAt_extChartAt x
  have heq : g =ᶠ[𝓝 (f x)] fun y => c.symm (i (d y)) := by
    rw [← map_nhds_eq_of_contMDiffAt_bijective_mfderiv_modelSpaces hf hbij]
    change ∀ᶠ z in 𝓝 x, g (f z) = c.symm (i (d (f z)))
    filter_upwards [hleft, hc.tendsto.eventually hil,
      (isOpen_extChartAt_source (I := 𝓘(ℝ, E)) x).mem_nhds (mem_extChartAt_source x)]
      with z hz hzi hzc
    have hAz : A (c z) = d (f z) := by
      simp only [A, writtenInExtChartAt, Function.comp_apply]
      rw [c.left_inv hzc]
    rw [hz, ← hAz, hzi, c.left_inv hzc]
  have hd : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ d (f x) := contMDiffAt_extChartAt
  have hi' : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ i (d (f x)) := by
    rw [← hAx]
    exact hi.contMDiffAt
  have hcs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm (i (d (f x))) := by
    rw [← hAx, hix]
    exact (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x).mem_nhds (mem_extChartAt_target x))
  exact (hcs.comp (f x) (hi'.comp (f x) hd)).congr_of_eventuallyEq heq

end Poincare.Geometry.Manifold
