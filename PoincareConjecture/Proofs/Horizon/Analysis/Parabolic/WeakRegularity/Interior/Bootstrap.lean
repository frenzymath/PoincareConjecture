




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Mollification
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.ConstantEnergyIdentity







open Set MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U : Set (Spacetime n)}






theorem spatialDeriv_lebesgueConvolution_on
    {u η : Spacetime n → ℝ} {V K : Set (Spacetime n)}
    (hV : IsOpen V) (hK : IsCompact K) (hu : ContinuousOn u K)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : ∀ z ∈ V, tsupport (translatedKernel η z) ⊆ K)
    {z : Spacetime n} (hz : z ∈ V) (i : Fin n) :
    spatialDeriv i (lebesgueConvolution η u) z =
      lebesgueConvolution (fun y => fderiv ℝ η y (spatialDirection i)) u z := by
  exact fderiv_lebesgueConvolution_on hV hK hu hη hηc hs hz
    (spatialDirection i)

theorem timeDeriv_lebesgueConvolution_on
    {u η : Spacetime n → ℝ} {V K : Set (Spacetime n)}
    (hV : IsOpen V) (hK : IsCompact K) (hu : ContinuousOn u K)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : ∀ z ∈ V, tsupport (translatedKernel η z) ⊆ K)
    {z : Spacetime n} (hz : z ∈ V) :
    timeDeriv (lebesgueConvolution η u) z =
      lebesgueConvolution (fun y => fderiv ℝ η y (0, 1)) u z := by
  exact fderiv_lebesgueConvolution_on hV hK hu hη hηc hs hz (0, 1)




theorem frozen_principal_hessian_bound
    {C : Coefficients n} {z : Spacetime n} {κ : ℝ}
    (hκ : 0 < κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, C.principal i j z * ξ i * ξ j)
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) :
    κ ^ 2 * (∫ x, ∑ i, ∑ j, (spatialSecond i j v x) ^ 2) ≤
      ∫ x, (constantPrincipal (fun i j => C.principal i j z) v x) ^ 2 := by
  exact integral_principal_sq_ge hv hvc (le_of_lt hκ) hEll

theorem frozen_principal_l2_coercivity
    {C : Coefficients n} {z : Spacetime n} {κ : ℝ}
    (hsymm : ∀ i j, C.principal i j z = C.principal j i z)
    (hκ : 0 < κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, C.principal i j z * ξ i * ξ j)
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) :
    (∫ x, (timeDeriv v x) ^ 2) + κ ^ 2 *
        (∫ x, ∑ i, ∑ j, (spatialSecond i j v x) ^ 2) ≤
      ∫ x, (timeDeriv v x - constantPrincipal (fun i j => C.principal i j z) v x) ^ 2 := by
  exact constant_parabolic_l2_coercivity_smooth_compact_support hv hvc
    (integral_timeDeriv_mul_constantPrincipal_eq_zero hv hvc hsymm)
    (frozen_principal_hessian_bound hκ hEll hv hvc)


theorem continuousOn_contDiffOn_zero {u : Spacetime n → ℝ}
    (hu : ContinuousOn u U) : ContDiffOn ℝ 0 u U := by
  exact contDiffOn_zero.mpr hu






theorem variable_principal_energy_absorption
    {κ ε H R V : ℝ}
    (hfrozen : κ ^ 2 * H ≤ R)
    (hperturb : R ≤ 2 * V + 2 * ε ^ 2 * H)
    (hsmall : 2 * ε ^ 2 < κ ^ 2) :
    H ≤ 2 * V / (κ ^ 2 - 2 * ε ^ 2) := by
  have hden : 0 < κ ^ 2 - 2 * ε ^ 2 := by
    nlinarith
  apply (le_div_iff₀ hden).2
  nlinarith [hfrozen, hperturb]




theorem young_flux_absorption
    {f g : Spacetime n → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hf : Integrable (fun x => f x ^ 2))
    (hg : Integrable (fun x => g x ^ 2))
    (hfg : Integrable (fun x => f x * g x)) :
    |∫ x, f x * g x| ≤
      δ * (∫ x, g x ^ 2) + (1 / (4 * δ)) * (∫ x, f x ^ 2) := by
  have hsum : Integrable (fun x =>
      δ * g x ^ 2 + (1 / (4 * δ)) * f x ^ 2) :=
    (hg.const_mul δ).add (hf.const_mul (1 / (4 * δ)))
  have hpoint : ∀ x, |f x * g x| ≤
      δ * g x ^ 2 + (1 / (4 * δ)) * f x ^ 2 := by
    intro x
    have hsq : 0 ≤ (2 * δ * |g x| - |f x|) ^ 2 := sq_nonneg _
    have hδ' : 0 < 4 * δ := by positivity
    have hinv : (4 * δ) * (1 / (4 * δ)) = 1 := by
      field_simp
    have hbase : |f x| * |g x| ≤
        δ * |g x| ^ 2 + (1 / (4 * δ)) * |f x| ^ 2 := by
      nlinarith
    simpa only [abs_mul, sq_abs] using hbase
  have hmono := integral_mono_ae hfg.norm hsum
    (Filter.Eventually.of_forall hpoint)
  calc
    |∫ x, f x * g x| ≤ ∫ x, |f x * g x| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (f := fun x => f x * g x))
    _ ≤ ∫ x, (δ * g x ^ 2 + (1 / (4 * δ)) * f x ^ 2) := hmono
    _ = δ * (∫ x, g x ^ 2) + (1 / (4 * δ)) * (∫ x, f x ^ 2) := by
      rw [integral_add (hg.const_mul δ) (hf.const_mul (1 / (4 * δ))),
        integral_const_mul, integral_const_mul]

theorem integral_sq_add_le
    {f g : Spacetime n → ℝ}
    (hf : Integrable (fun x => f x ^ 2))
    (hg : Integrable (fun x => g x ^ 2))
    (hfg : Integrable (fun x => (f x + g x) ^ 2)) :
    (∫ x, (f x + g x) ^ 2) ≤
      2 * (∫ x, f x ^ 2) + 2 * (∫ x, g x ^ 2) := by
  have hsum : Integrable (fun x => 2 * f x ^ 2 + 2 * g x ^ 2) :=
    (hf.const_mul 2).add (hg.const_mul 2)
  have hpoint : ∀ x, (f x + g x) ^ 2 ≤ 2 * f x ^ 2 + 2 * g x ^ 2 := by
    intro x
    nlinarith [sq_nonneg (f x - g x)]
  have hmono := integral_mono_ae hfg hsum
    (Filter.Eventually.of_forall hpoint)
  calc
    (∫ x, (f x + g x) ^ 2) ≤ ∫ x, (2 * f x ^ 2 + 2 * g x ^ 2) := hmono
    _ = 2 * (∫ x, f x ^ 2) + 2 * (∫ x, g x ^ 2) := by
      rw [integral_add (hf.const_mul 2) (hg.const_mul 2),
        integral_const_mul, integral_const_mul]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
