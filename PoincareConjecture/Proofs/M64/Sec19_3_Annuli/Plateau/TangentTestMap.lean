import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ChartReaderProjection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m64_exists_smooth_tangent_test (q : M) (w : TangentSpace (𝓡 n) q) :
    ∃ f : LoopPlane → M, ContMDiff (𝓡 2) (𝓡 n) 1 f ∧ f 0 = q ∧
      mfderiv (𝓡 2) (𝓡 n) f 0 (EuclideanSpace.basisFun (Fin 2) ℝ 0) = w := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) q
  have hq : q ∈ c.source := mem_chart_source _ q
  have hc : c.MDifferentiable (𝓡 n) (𝓡 n) := mdifferentiable_chart q
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hq))
  let a : EuclideanSpace ℝ (Fin n) := mfderiv (𝓡 n) (𝓡 n) c q w
  let delta := r / (2 * (‖a‖ + 1))
  have hdelta : 0 < delta := div_pos hr (by positivity)
  have hsmall : delta * ‖a‖ < r := by
    dsimp only [delta]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * (‖a‖ + 1))]
    nlinarith [norm_nonneg a]
  let F : LoopPlane → EuclideanSpace ℝ (Fin n) :=
    fun z => c q + (delta * Real.sin (z 0 / delta)) • a
  have hF0 : F 0 = c q := by simp [F]
  have hF : ContDiff ℝ 1 F := by
    dsimp only [F]
    fun_prop
  have hFt (z : LoopPlane) : F z ∈ c.target := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖F z - c q‖ = delta * |Real.sin (z 0 / delta)| * ‖a‖ := by
        simp only [F, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul,
          abs_of_pos hdelta]
      _ ≤ delta * ‖a‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right hdelta.le (Real.abs_sin_le_one _)) (norm_nonneg _)
      _ < r := hsmall
  have hs : HasFDerivAt (fun z : LoopPlane => delta * Real.sin (z 0 / delta))
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) 0 := by
    have hlin := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := (0 : LoopPlane))
    have h := (hlin.mul_const delta⁻¹).sin.const_mul delta
    simpa [div_eq_mul_inv, hdelta.ne'] using h
  have hDF : HasFDerivAt F ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight a) 0 :=
    (hs.smul_const a).const_add (c q)
  let f := c.symm ∘ F
  have hf : ContMDiff (𝓡 2) (𝓡 n) 1 f :=
    (contMDiffOn_chart_symm : ContMDiffOn (𝓡 n) (𝓡 n) 1 c.symm c.target).comp_contMDiff
      (contMDiff_iff_contDiff.mpr hF) hFt
  refine ⟨f, hf, ?_, ?_⟩
  · change c.symm (F 0) = q
    rw [hF0, c.left_inv hq]
  · have hcomp := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 n) (I'' := 𝓡 n) 0
      (hc.mdifferentiableAt_symm (hFt 0)) hDF.differentiableAt.mdifferentiableAt
    change mfderiv (𝓡 2) (𝓡 n) (c.symm ∘ F) 0 _ = w
    rw [hcomp, mfderiv_eq_fderiv, hDF.fderiv, hF0]
    have hid := congrArg (fun T => T w) (hc.symm_comp_deriv hq)
    erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
    have hb : (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) = 1 := by simp
    erw [hb, one_smul]
    change mfderiv (𝓡 n) (𝓡 n) c.symm (c q) a = w at hid
    exact hid

end PoincareConjecture
