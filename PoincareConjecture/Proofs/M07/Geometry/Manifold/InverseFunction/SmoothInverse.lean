import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

set_option backward.isDefEq.respectTransparency false in

theorem contMDiffAt_of_local_left_inverse {f : M → N} {g : N → M} {x : M}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hbij : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hleft : ∀ᶠ z in 𝓝 x, g (f z) = z) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ g (f x) := by
  let c := extChartAt (𝓡 n) x
  let d := extChartAt (𝓡 n) (f x)
  let F := writtenInExtChartAt (𝓡 n) (𝓡 n) x f
  have hF : ContDiffAt ℝ ∞ F (c x) := by
    simpa [F, c, writtenInExtChartAt, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp hf).2
  have hderiv : mfderiv (𝓡 n) (𝓡 n) f x = fderiv ℝ F (c x) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [F, c]
  have hFbij : Function.Bijective (fderiv ℝ F (c x)) := by
    rwa [hderiv] at hbij
  let e := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hdF : HasFDerivAt F (e : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) (c x) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  let i := hF.localInverse hdF (by simp)
  have hi : ContDiffAt ℝ ∞ i (F (c x)) := hF.to_localInverse hdF (by simp)
  have hix : i (F (c x)) = c x := hF.localInverse_apply_image hdF (by simp)
  have hFx : F (c x) = d (f x) := by simp [F, c, d, writtenInExtChartAt]
  have hil : ∀ᶠ z in 𝓝 (c x), i (F z) = z :=
    (hF.hasStrictFDerivAt' hdF (by simp)).eventually_left_inverse
  have hc : ContinuousAt c x := continuousAt_extChartAt x
  have heq : g =ᶠ[𝓝 (f x)] fun y => c.symm (i (d y)) := by
    rw [← map_nhds_eq_of_contMDiffAt_mfderiv_bijective hf hbij]
    change ∀ᶠ z in 𝓝 x, g (f z) = c.symm (i (d (f z)))
    filter_upwards [hleft, hc.tendsto.eventually hil,
      (isOpen_extChartAt_source (I := 𝓡 n) x).mem_nhds (mem_extChartAt_source x)]
      with z hz hzi hzc
    have hFz : F (c z) = d (f z) := by
      simp only [F, writtenInExtChartAt, Function.comp_apply]
      rw [c.left_inv hzc]
    rw [hz, ← hFz, hzi, c.left_inv hzc]
  have hd : ContMDiffAt (𝓡 n) (𝓡 n) ∞ d (f x) := contMDiffAt_extChartAt
  have hi' : ContMDiffAt (𝓡 n) (𝓡 n) ∞ i (d (f x)) := by
    rw [← hFx]
    exact hi.contMDiffAt
  have hcs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (i (d (f x))) := by
    rw [← hFx, hix]
    exact (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds (mem_extChartAt_target x))
  exact (hcs.comp (f x) (hi'.comp (f x) hd)).congr_of_eventuallyEq heq

end Poincare
