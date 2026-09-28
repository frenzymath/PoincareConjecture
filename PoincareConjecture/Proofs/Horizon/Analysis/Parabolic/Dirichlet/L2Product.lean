import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

namespace Poincare.Analysis.Dirichlet

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

theorem memLp_tensor (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    MemLp (fun z : α × β => f z.1 * g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq
    ((Lp.aestronglyMeasurable f).comp_fst.mul (Lp.aestronglyMeasurable g).comp_snd)).mpr
  simpa only [Pi.mul_apply, mul_pow] using
    (Lp.memLp f).integrable_sq.mul_prod (Lp.memLp g).integrable_sq

def tensorL2 (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) : Lp ℝ 2 (μ.prod ν) :=
  (memLp_tensor f g).toLp (fun z : α × β => f z.1 * g z.2)

theorem tensorL2_ae (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    (tensorL2 f g : α × β → ℝ) =ᵐ[μ.prod ν] fun z => f z.1 * g z.2 :=
  (memLp_tensor f g).coeFn_toLp

theorem inner_tensorL2 [SFinite μ] [SFinite ν]
    (f u : Lp ℝ 2 μ) (g v : Lp ℝ 2 ν) :
    ⟪tensorL2 f g, tensorL2 u v⟫_ℝ = ⟪f, u⟫_ℝ * ⟪g, v⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [tensorL2_ae f g, tensorL2_ae u v] with z hfg huv
  simp only [hfg, huv, RCLike.inner_apply, conj_trivial]
  ring

@[simp] theorem norm_tensorL2 [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    ‖tensorL2 f g‖ = ‖f‖ * ‖g‖ := by
  have hs : ‖tensorL2 f g‖ ^ 2 = (‖f‖ * ‖g‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_tensorL2,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hs

theorem tensorL2_add_left (f u : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    tensorL2 (f + u) g = tensorL2 f g + tensorL2 u g := by
  apply Lp.ext
  filter_upwards [tensorL2_ae (f + u) g, tensorL2_ae f g, tensorL2_ae u g,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_add f u),
    Lp.coeFn_add (tensorL2 f g) (tensorL2 u g)] with z h1 h2 h3 h4 h5
  simp only [Function.comp_def, Pi.add_apply] at h4 h5
  rw [h1, h5, h2, h3, h4]
  ring

theorem tensorL2_add_right (f : Lp ℝ 2 μ) (g v : Lp ℝ 2 ν) :
    tensorL2 f (g + v) = tensorL2 f g + tensorL2 f v := by
  apply Lp.ext
  filter_upwards [tensorL2_ae f (g + v), tensorL2_ae f g, tensorL2_ae f v,
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_add g v),
    Lp.coeFn_add (tensorL2 f g) (tensorL2 f v)] with z h1 h2 h3 h4 h5
  simp only [Function.comp_def, Pi.add_apply] at h4 h5
  rw [h1, h5, h2, h3, h4]
  ring

theorem tensorL2_smul_left (c : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    tensorL2 (c • f) g = c • tensorL2 f g := by
  apply Lp.ext
  filter_upwards [tensorL2_ae (c • f) g, tensorL2_ae f g,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_smul c f),
    Lp.coeFn_smul c (tensorL2 f g)] with z h1 h2 h3 h4
  simp only [Function.comp_def, Pi.smul_apply, smul_eq_mul] at h3 h4
  rw [h1, h4, h2, h3]
  ring

theorem tensorL2_smul_right (c : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    tensorL2 f (c • g) = c • tensorL2 f g := by
  apply Lp.ext
  filter_upwards [tensorL2_ae f (c • g), tensorL2_ae f g,
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_smul c g),
    Lp.coeFn_smul c (tensorL2 f g)] with z h1 h2 h3 h4
  simp only [Function.comp_def, Pi.smul_apply, smul_eq_mul] at h3 h4
  rw [h1, h4, h2, h3]
  ring

def tensorL2CLM [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := tensorL2 f
      map_add' := tensorL2_add_right f
      map_smul' := fun c g => tensorL2_smul_right c f g }
    ‖f‖ (fun g => (norm_tensorL2 f g).le)

@[simp] theorem tensorL2CLM_apply [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    tensorL2CLM f g = tensorL2 f g := rfl

theorem norm_tensorL2CLM_le [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) : ‖tensorL2CLM (ν := ν) f‖ ≤ ‖f‖ :=
  (tensorL2CLM f).opNorm_le_bound (norm_nonneg f)
    (fun g => (norm_tensorL2 f g).le)

end Poincare.Analysis.Dirichlet
