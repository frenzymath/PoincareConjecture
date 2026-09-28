import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology



theorem mfderiv_inverse_chart_comp_fderiv_coordinates
    {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : M) {φ : E → M} {x : E}
    (hφ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) φ x)
    (hq : φ x ∈ (extChartAt 𝓘(ℝ, F) q).source) :
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (extChartAt 𝓘(ℝ, F) q).symm
      ((extChartAt 𝓘(ℝ, F) q) (φ x))).comp
        (fderiv ℝ ((extChartAt 𝓘(ℝ, F) q) ∘ φ) x) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) φ x := by
  let c := extChartAt 𝓘(ℝ, F) q
  have hc : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) c (φ x) :=
    ((contMDiffOn_extChartAt (I := 𝓘(ℝ, F)) (x := q) (n := ∞)).contMDiffAt
      (by simpa only [extChartAt_source] using
        (isOpen_extChartAt_source q).mem_nhds hq)).mdifferentiableAt (by simp)
  have hci : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) c.symm (c (φ x)) :=
    ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) q (c.map_source hq)).contMDiffAt
      (extChartAt_target_mem_nhds' (c.map_source hq))).mdifferentiableAt (by simp)
  have hlocal : c.symm ∘ (c ∘ φ) =ᶠ[𝓝 x] φ := by
    filter_upwards [hφ.continuousAt.tendsto.eventually
      ((isOpen_extChartAt_source q).mem_nhds hq)] with y hy
    exact c.left_inv hy
  have hd := mfderiv_comp x hci (hc.comp x hφ)
  rw [mfderiv_eq_fderiv] at hd
  exact hd.symm.trans hlocal.mfderiv_eq
