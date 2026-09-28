import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.L2KernelOperator
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SpectralSemigroup

set_option autoImplicit false

noncomputable section

namespace Poincare.Analysis.Dirichlet.Spectral

open MeasureTheory Filter
open scoped InnerProductSpace NNReal

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

def kernelL2 (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (lam : ι → ℝ≥0) (t : ℝ≥0) :
    Lp ℝ 2 (μ.prod μ) :=
  ∑' i, Real.exp (-(lam i : ℝ) * (t : ℝ)) • tensorL2 (b i) (b i)

theorem summable_norm_kernelL2 [SFinite μ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (lam : ι → ℝ≥0) (t : ℝ≥0)
    (hs : Summable (fun i => Real.exp (-(lam i : ℝ) * (t : ℝ)))) :
    Summable (fun i => ‖Real.exp (-(lam i : ℝ) * (t : ℝ)) •
      tensorL2 (b i) (b i)‖) := by
  simpa only [norm_smul, norm_tensorL2, b.orthonormal.norm_eq_one,
    one_mul, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le] using hs

theorem kernelL2_hasSum [SFinite μ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (lam : ι → ℝ≥0) (t : ℝ≥0)
    (hs : Summable (fun i => Real.exp (-(lam i : ℝ) * (t : ℝ)))) :
    HasSum (fun i => Real.exp (-(lam i : ℝ) * (t : ℝ)) •
      tensorL2 (b i) (b i)) (kernelL2 b lam t) :=
  (summable_norm_kernelL2 b lam t hs).of_norm.hasSum

theorem inner_kernelL2_tensor [SFinite μ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (lam : ι → ℝ≥0) (t : ℝ≥0)
    (hs : Summable (fun i => Real.exp (-(lam i : ℝ) * (t : ℝ))))
    (f h : Lp ℝ 2 μ) :
    ⟪kernelL2 b lam t, tensorL2 h f⟫_ℝ = ⟪heat b lam t f, h⟫_ℝ := by
  have hk := (kernelL2_hasSum b lam t hs).mapL (innerSL ℝ (tensorL2 h f))
  have hh := (heat_hasSum b lam t f).mapL (innerSL ℝ h)
  have heq : HasSum
      (fun i => Real.exp (-(lam i : ℝ) * (t : ℝ)) * (b.repr f i * ⟪h, b i⟫_ℝ))
      ⟪tensorL2 h f, kernelL2 b lam t⟫_ℝ := by
    convert! hk using 1
    ext i
    simp only [innerSL_apply_apply, real_inner_smul_right, inner_tensorL2,
      HilbertBasis.repr_apply_apply]
    rw [real_inner_comm f (b i)]
    ring
  have heq' : HasSum
      (fun i => Real.exp (-(lam i : ℝ) * (t : ℝ)) * (b.repr f i * ⟪h, b i⟫_ℝ))
      ⟪h, heat b lam t f⟫_ℝ := by
    convert! hh using 1
    ext i
    simp only [innerSL_apply_apply, real_inner_smul_right]
    ring
  simpa only [real_inner_comm (kernelL2 b lam t), real_inner_comm (heat b lam t f)]
    using heq.unique heq'

theorem integrable_kernelL2_pair
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (lam : ι → ℝ≥0) (t : ℝ≥0)
    (f h : Lp ℝ 2 μ) :
    Integrable (fun z : α × α => kernelL2 b lam t z * h z.1 * f z.2)
      (μ.prod μ) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (kernelL2 b lam t) (tensorL2 h f)).congr
  filter_upwards [tensorL2_ae h f] with z hz
  simp only [hz, RCLike.inner_apply, conj_trivial]
  ring

theorem integral_kernelL2_pair [SFinite μ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (lam : ι → ℝ≥0) (t : ℝ≥0)
    (hs : Summable (fun i => Real.exp (-(lam i : ℝ) * (t : ℝ))))
    (f h : Lp ℝ 2 μ) :
    (∫ z : α × α, kernelL2 b lam t z * h z.1 * f z.2 ∂(μ.prod μ)) =
      ⟪heat b lam t f, h⟫_ℝ := by
  rw [← inner_kernelL2_tensor b lam t hs f h, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensorL2_ae h f] with z hz
  simp only [hz, RCLike.inner_apply, conj_trivial]
  ring

theorem kernelOperator_kernelL2 [SFinite μ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (lam : ι → ℝ≥0) (t : ℝ≥0)
    (hs : Summable (fun i => Real.exp (-(lam i : ℝ) * (t : ℝ)))) :
    kernelOperator (kernelL2 b lam t) = heat b lam t := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro h
  rw [inner_kernelOperator, inner_kernelL2_tensor b lam t hs f h]

theorem kernelL2_integral_ae [IsFiniteMeasure μ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (lam : ι → ℝ≥0) (t : ℝ≥0)
    (hs : Summable (fun i => Real.exp (-(lam i : ℝ) * (t : ℝ))))
    (f : Lp ℝ 2 μ) :
    (heat b lam t f : α → ℝ) =ᵐ[μ]
      fun x => ∫ y, kernelL2 b lam t (x, y) * f y ∂μ := by
  rw [← kernelOperator_kernelL2 b lam t hs]
  exact kernelOperator_ae _ f

end Poincare.Analysis.Dirichlet.Spectral
