import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]

set_option backward.isDefEq.respectTransparency false in


theorem map_nhds_eq_of_contMDiffAt_mfderiv_bijective {f : M → N} {x : M}
    (hf : ContMDiffAt I J ∞ f x)
    (hbij : Function.Bijective (mfderiv I J f x)) :
    map f (𝓝 x) = 𝓝 (f x) := by
  let c := extChartAt I x
  let d := extChartAt J (f x)
  let f' := writtenInExtChartAt I J x f
  have hF : ContDiffAt ℝ 1 f' (c x) := by
    simpa [f', c, writtenInExtChartAt, I.range_eq_univ, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))).2
  have hderiv : mfderiv I J f x = fderiv ℝ f' (c x) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [f', c, I.range_eq_univ]
  have hFbij : Function.Bijective (fderiv ℝ f' (c x)) := by
    rwa [hderiv] at hbij
  let e := ContinuousLinearEquiv.ofBijective (fderiv ℝ f' (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hstrict : HasStrictFDerivAt f' (e : E →L[ℝ] F) (c x) :=
    hF.hasStrictFDerivAt' (hF.differentiableAt (by norm_num)).hasFDerivAt (by norm_num)
  have hcmap : map c.symm (𝓝 (c x)) = 𝓝 x := by
    simpa [c, I.range_eq_univ] using map_extChartAt_symm_nhdsWithin_range (I := I) x
  have hdmap : map d.symm (𝓝 (d (f x))) = 𝓝 (f x) := by
    simpa [d, J.range_eq_univ] using map_extChartAt_symm_nhdsWithin_range (I := J) (f x)
  have hfc : Tendsto (f ∘ c.symm) (𝓝 (c x)) (𝓝 (f x)) :=
    hf.continuousAt.tendsto.comp hcmap.le
  have heq : d.symm ∘ f' =ᶠ[𝓝 (c x)] f ∘ c.symm := by
    filter_upwards [hfc.eventually
      ((isOpen_extChartAt_source (I := J) (f x)).mem_nhds
        (mem_extChartAt_source (I := J) (f x)))] with y hy
    exact d.left_inv hy
  have hFx : f' (c x) = d (f x) := by simp [f', c, d, writtenInExtChartAt]
  calc
    map f (𝓝 x) = map (f ∘ c.symm) (𝓝 (c x)) := by rw [← map_map, hcmap]
    _ = map (d.symm ∘ f') (𝓝 (c x)) := map_congr heq.symm
    _ = map d.symm (map f' (𝓝 (c x))) := (map_map ..).symm
    _ = map d.symm (𝓝 (f' (c x))) := by rw [hstrict.map_nhds_eq_of_equiv]
    _ = 𝓝 (f x) := by rw [hFx, hdmap]



theorem isOpen_image_of_contMDiffOn_mfderiv_bijective {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I J ∞ f U)
    (hbij : ∀ x ∈ U, Function.Bijective (mfderiv I J f x)) :
    IsOpen (f '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    (hf.contMDiffAt (hU.mem_nhds hx)) (hbij x hx)]
  exact image_mem_map (hU.mem_nhds hx)

end PoincareConjecture.M34
