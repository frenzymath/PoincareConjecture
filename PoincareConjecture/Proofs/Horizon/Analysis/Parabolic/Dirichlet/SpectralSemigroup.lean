import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Tannery













set_option autoImplicit false

noncomputable section

namespace Poincare.Analysis.Dirichlet.Spectral

open Filter
open scoped Topology InnerProductSpace NNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def coefficient (lam : ι → ℝ≥0) (t : ℝ≥0) (i : ι) : ℝ :=
  Real.exp (-(lam i : ℝ) * (t : ℝ))

theorem coefficient_pos (lam : ι → ℝ≥0) (t : ℝ≥0) (i : ι) :
    0 < coefficient lam t i := Real.exp_pos _

theorem coefficient_le_one (lam : ι → ℝ≥0) (t : ℝ≥0) (i : ι) :
    coefficient lam t i ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (lam i).coe_nonneg) t.coe_nonneg

theorem norm_coefficient_mul_le (lam : ι → ℝ≥0) (t : ℝ≥0) (i : ι) (r : ℝ) :
    ‖coefficient lam t i * r‖ ≤ ‖r‖ := by
  rw [norm_mul, Real.norm_of_nonneg (coefficient_pos lam t i).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (coefficient_le_one lam t i)


def multiplier (lam : ι → ℝ≥0) (t : ℝ≥0) :
    lp (fun _ : ι => ℝ) 2 →L[ℝ] lp (fun _ : ι => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => coefficient lam t i * x i,
        x.property.mono' (fun i => norm_coefficient_mul_le lam t i (x i))⟩
      map_add' := by
        intro x y
        ext i
        change coefficient lam t i * (x i + y i) =
          coefficient lam t i * x i + coefficient lam t i * y i
        ring
      map_smul' := by
        intro r x
        ext i
        change coefficient lam t i * (r * x i) = r * (coefficient lam t i * x i)
        ring }
    1 (fun x => by
      simpa using lp.norm_mono (p := 2) (by norm_num)
        (fun i => norm_coefficient_mul_le lam t i (x i)))

@[simp] theorem multiplier_apply (lam : ι → ℝ≥0) (t : ℝ≥0)
    (x : lp (fun _ : ι => ℝ) 2) (i : ι) :
    multiplier lam t x i = coefficient lam t i * x i := rfl


def heat (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (t : ℝ≥0) : H →L[ℝ] H :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((multiplier lam t).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem heat_repr (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (t : ℝ≥0)
    (u : H) (i : ι) :
    b.repr (heat b lam t u) i = Real.exp (-(lam i : ℝ) * (t : ℝ)) * b.repr u i := by
  change b.repr (b.repr.symm (multiplier lam t (b.repr u))) i = _
  rw [b.repr.apply_symm_apply]
  rfl

theorem heat_hasSum (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (t : ℝ≥0) (u : H) :
    HasSum (fun i => (Real.exp (-(lam i : ℝ) * (t : ℝ)) * b.repr u i) • b i)
      (heat b lam t u) := by
  simpa only [heat_repr] using b.hasSum_repr (heat b lam t u)

theorem norm_heat_apply_le (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (t : ℝ≥0)
    (u : H) : ‖heat b lam t u‖ ≤ ‖u‖ := by
  rw [← b.repr.norm_map (heat b lam t u), ← b.repr.norm_map u]
  apply lp.norm_mono (by norm_num)
  intro i
  rw [heat_repr]
  exact norm_coefficient_mul_le lam t i _

theorem norm_heat_le (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (t : ℝ≥0) :
    ‖heat b lam t‖ ≤ 1 :=
  (heat b lam t).opNorm_le_bound zero_le_one (fun u => by
    simpa using norm_heat_apply_le b lam t u)

@[simp] theorem heat_zero (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) :
    heat b lam 0 = ContinuousLinearMap.id ℝ H := by
  ext u
  apply b.repr.injective
  ext i
  simp [heat_repr]

theorem heat_add (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (s t : ℝ≥0) :
    heat b lam (s + t) = (heat b lam s).comp (heat b lam t) := by
  ext u
  apply b.repr.injective
  ext i
  simp only [ContinuousLinearMap.comp_apply, heat_repr, NNReal.coe_add,
    mul_add, Real.exp_add, mul_assoc]

theorem heat_isSelfAdjoint [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (t : ℝ≥0) :
    IsSelfAdjoint (heat b lam t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  change ⟪heat b lam t u, v⟫_ℝ = ⟪u, heat b lam t v⟫_ℝ
  rw [← b.repr.inner_map_map (heat b lam t u) v,
    ← b.repr.inner_map_map u (heat b lam t v), lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [heat_repr, RCLike.inner_apply, conj_trivial]
  ring

theorem norm_sq_eq_tsum (b : HilbertBasis ι ℝ H) (u : H) :
    ‖u‖ ^ 2 = ∑' i, (b.repr u i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.repr.inner_map_map u u, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp [pow_two]

theorem summable_repr_sq (b : HilbertBasis ι ℝ H) (u : H) :
    Summable (fun i => (b.repr u i) ^ 2) := by
  simpa [pow_two] using (lp.hasSum_inner (𝕜 := ℝ) (b.repr u) (b.repr u)).summable

private theorem coefficient_sub_sq_le (lam : ι → ℝ≥0) (s t : ℝ≥0) (i : ι) :
    (coefficient lam s i - coefficient lam t i) ^ 2 ≤ 1 := by
  have hs := coefficient_pos lam s i
  have ht := coefficient_pos lam t i
  have hs' := coefficient_le_one lam s i
  have ht' := coefficient_le_one lam t i
  nlinarith [sq_nonneg (coefficient lam s i), sq_nonneg (coefficient lam t i)]

theorem continuous_heat (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (u : H) :
    Continuous (fun t : ℝ≥0 => heat b lam t u) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hsum : Tendsto
      (fun s : ℝ≥0 => ∑' i,
        ((coefficient lam s i - coefficient lam t i) * b.repr u i) ^ 2)
      (𝓝 t) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence
      (summable_repr_sq b u) (𝓕 := 𝓝 t)
      (f := fun s i => ((coefficient lam s i - coefficient lam t i) * b.repr u i) ^ 2)
      (g := fun _ : ι => (0 : ℝ)) ?_ ?_
    · simpa using h
    · intro i
      have hc : Continuous (fun s : ℝ≥0 => coefficient lam s i) := by
        unfold coefficient
        fun_prop
      convert (((hc.continuousAt.tendsto.sub_const (coefficient lam t i)).mul_const
        (b.repr u i)).pow 2) using 1
      simp
    · exact Filter.Eventually.of_forall fun s i => by
        rw [Real.norm_of_nonneg (sq_nonneg _), mul_pow]
        simpa using mul_le_mul_of_nonneg_right
          (coefficient_sub_sq_le lam s t i) (sq_nonneg (b.repr u i))
  have hnorm : Tendsto (fun s : ℝ≥0 => ‖heat b lam s u - heat b lam t u‖ ^ 2)
      (𝓝 t) (𝓝 0) := by
    convert hsum using 1
    funext s
    rw [norm_sq_eq_tsum b]
    apply tsum_congr
    intro i
    simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, heat_repr, coefficient]
    ring
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hnorm
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    dist_eq_norm] using hroot

end Poincare.Analysis.Dirichlet.Spectral
