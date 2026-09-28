import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialReflection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace PoincareConjecture

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "R" => m60PlaneReflection

theorem m64RadialCorrect_fderiv_lower
    (f h : LoopPlane → E) {p : LoopPlane} (hp : p 1 < 0) :
    fderiv ℝ (m64RadialCorrect f h) p = fderiv ℝ h p := by
  have heq : m64RadialCorrect f h =ᶠ[𝓝 p] h := by
    filter_upwards [(isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous
      continuous_const).mem_nhds hp] with q hq
    exact m64RadialCorrect_lower f h hq.le
  exact heq.fderiv_eq

theorem m64RadialCorrect_fderiv_upper
    {f h : LoopPlane → E} (hf : Differentiable ℝ f) (hh : Differentiable ℝ h)
    {p : LoopPlane} (hp : 0 < p 1) (v : LoopPlane) :
    fderiv ℝ (m64RadialCorrect f h) p v =
      fderiv ℝ f p v - fderiv ℝ f (R p) (R v) + fderiv ℝ h p v := by
  have heq : m64RadialCorrect f h =ᶠ[𝓝 p] (fun q => f q - f (R q) + h q) := by
    filter_upwards [(isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous).mem_nhds hp] with q hq
    exact m64RadialCorrect_upper f h hq.le
  have hd := ((hf p).hasFDerivAt.sub ((hf (R p)).hasFDerivAt.comp p
    m60PlaneReflection.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)).add
      (hh p).hasFDerivAt
  rw [heq.fderiv_eq]
  simpa +instances only [Pi.add_apply, Pi.sub_apply, Function.comp_def, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply] using! congrArg (fun D => D v) hd.fderiv

theorem m64RadialCorrect_differentiable_ae
    {f h : LoopPlane → E} (hf : Differentiable ℝ f) (hh : Differentiable ℝ h) :
    ∀ᵐ p : LoopPlane ∂volume, DifferentiableAt ℝ (m64RadialCorrect f h) p := by
  have hn : ∀ᵐ p : LoopPlane ∂volume, p 1 ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using m64_radial_line_null 0
  filter_upwards [hn] with p hp
  rcases lt_or_gt_of_ne hp with hl | hr
  · apply (hh p).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous
      continuous_const).mem_nhds hl] with q hq
    exact m64RadialCorrect_lower f h hq.le
  · apply ((hf p).sub ((hf (R p)).comp p m60PlaneReflection.differentiableAt) |>.add
      (hh p)).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous).mem_nhds hr] with q hq
    exact m64RadialCorrect_upper f h hq.le

theorem m64_norm_sub_add_sq_le (u v w : E) :
    ‖u - v + w‖ ^ 2 ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have ht : ‖u - v + w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ := by
    have h0 := norm_add_le (u - v) w
    have h1 := norm_sub_le u v
    linarith
  calc
    _ ≤ (‖u‖ + ‖v‖ + ‖w‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
    _ ≤ _ := by
      nlinarith [sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖u‖ - ‖w‖), sq_nonneg (‖v‖ - ‖w‖)]

theorem m64PlaneReflection_column_norm (D : LoopPlane →L[ℝ] E) (i : Fin 2) :
    ‖D (R (EuclideanSpace.single i 1))‖ = ‖D (EuclideanSpace.single i 1)‖ := by
  have h0 : R (EuclideanSpace.single (0 : Fin 2) 1) = EuclideanSpace.single (0 : Fin 2) 1 := by
    simpa only [EuclideanSpace.basisFun_apply] using m60PlaneReflection_basis_zero
  have h1 : R (EuclideanSpace.single (1 : Fin 2) 1) = -EuclideanSpace.single (1 : Fin 2) 1 := by
    simpa only [EuclideanSpace.basisFun_apply] using m60PlaneReflection_basis_one
  fin_cases i
  · change ‖D (R (EuclideanSpace.single (0 : Fin 2) 1))‖ =
      ‖D (EuclideanSpace.single (0 : Fin 2) 1)‖
    rw [h0]
  · change ‖D (R (EuclideanSpace.single (1 : Fin 2) 1))‖ =
      ‖D (EuclideanSpace.single (1 : Fin 2) 1)‖
    rw [h1, map_neg, norm_neg]

theorem m64RadialCorrect_column_bound_ae
    {f h : LoopPlane → E} (hf : Differentiable ℝ f) (hh : Differentiable ℝ h) (i : Fin 2) :
    ∀ᵐ p : LoopPlane ∂volume,
      ‖fderiv ℝ (m64RadialCorrect f h) p (EuclideanSpace.single i 1)‖ ^ 2 ≤
        3 * (‖fderiv ℝ f p (EuclideanSpace.single i 1)‖ ^ 2 +
          ‖fderiv ℝ f (R p) (EuclideanSpace.single i 1)‖ ^ 2 +
          ‖fderiv ℝ h p (EuclideanSpace.single i 1)‖ ^ 2) := by
  have hn : ∀ᵐ p : LoopPlane ∂volume, p 1 ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using m64_radial_line_null 0
  filter_upwards [hn] with p hp
  rcases lt_or_gt_of_ne hp with hl | hr
  · rw [m64RadialCorrect_fderiv_lower f h hl]
    nlinarith [sq_nonneg ‖fderiv ℝ f p (EuclideanSpace.single i 1)‖,
      sq_nonneg ‖fderiv ℝ f (R p) (EuclideanSpace.single i 1)‖,
      sq_nonneg ‖fderiv ℝ h p (EuclideanSpace.single i 1)‖]
  · rw [m64RadialCorrect_fderiv_upper hf hh hr]
    simpa only [m64PlaneReflection_column_norm] using m64_norm_sub_add_sq_le
      (fderiv ℝ f p (EuclideanSpace.single i 1))
      (fderiv ℝ f (R p) (R (EuclideanSpace.single i 1)))
      (fderiv ℝ h p (EuclideanSpace.single i 1))

end PoincareConjecture
