import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

set_option backward.isDefEq.respectTransparency false in
theorem map_nhds_eq_of_contMDiffAt_mfderiv_bijective {f : M → N} {x : M}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hbij : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    map f (𝓝 x) = 𝓝 (f x) := by
  let c := extChartAt (𝓡 n) x
  let d := extChartAt (𝓡 n) (f x)
  let F := writtenInExtChartAt (𝓡 n) (𝓡 n) x f
  have hF : ContDiffAt ℝ 1 F (c x) := by
    simpa [F, c, writtenInExtChartAt, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))).2
  have hderiv : mfderiv (𝓡 n) (𝓡 n) f x = fderiv ℝ F (c x) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [F, c]
  have hFbij : Function.Bijective (fderiv ℝ F (c x)) := by
    rwa [hderiv] at hbij
  let e := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hstrict : HasStrictFDerivAt F (e : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) (c x) :=
    hF.hasStrictFDerivAt' (hF.differentiableAt (by norm_num)).hasFDerivAt (by norm_num)
  have hcmap : map c.symm (𝓝 (c x)) = 𝓝 x := by
    simpa [c] using map_extChartAt_symm_nhdsWithin_range (I := 𝓡 n) x
  have hdmap : map d.symm (𝓝 (d (f x))) = 𝓝 (f x) := by
    simpa [d] using map_extChartAt_symm_nhdsWithin_range (I := 𝓡 n) (f x)
  have hfc : Tendsto (f ∘ c.symm) (𝓝 (c x)) (𝓝 (f x)) :=
    hf.continuousAt.tendsto.comp hcmap.le
  have heq : d.symm ∘ F =ᶠ[𝓝 (c x)] f ∘ c.symm := by
    filter_upwards [hfc.eventually
      ((isOpen_extChartAt_source (I := 𝓡 n) (f x)).mem_nhds
        (mem_extChartAt_source (I := 𝓡 n) (f x)))] with y hy
    exact d.left_inv hy
  have hFx : F (c x) = d (f x) := by simp [F, c, d, writtenInExtChartAt]
  calc
    map f (𝓝 x) = map (f ∘ c.symm) (𝓝 (c x)) := by rw [← map_map, hcmap]
    _ = map (d.symm ∘ F) (𝓝 (c x)) := map_congr heq.symm
    _ = map d.symm (map F (𝓝 (c x))) := (map_map ..).symm
    _ = map d.symm (𝓝 (F (c x))) := by rw [hstrict.map_nhds_eq_of_equiv]
    _ = 𝓝 (f x) := by rw [hFx, hdmap]

end Poincare
