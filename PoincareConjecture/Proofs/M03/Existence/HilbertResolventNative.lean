import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum











set_option autoImplicit false

noncomputable section

namespace PoincareConjecture.HilbertResolventNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


def solution (J : V →L[ℝ] H) : H →L[ℝ] V := J.adjoint

theorem solution_pairing (J : V →L[ℝ] H) (f : H) (v : V) :
    inner ℝ v (solution J f) = inner ℝ (J v) f :=
  J.adjoint_inner_right v f

theorem solution_unique (J : V →L[ℝ] H) (f : H) (u : V)
    (hu : ∀ v : V, inner ℝ v u = inner ℝ (J v) f) : u = solution J f := by
  apply ext_inner_left ℝ
  intro v
  exact (hu v).trans (solution_pairing J f v).symm


def operator (J : V →L[ℝ] H) : H →L[ℝ] H := J.comp (solution J)

@[simp] theorem operator_apply (J : V →L[ℝ] H) (f : H) :
    operator J f = J (J.adjoint f) := rfl

theorem inner_operator_left (J : V →L[ℝ] H) (f g : H) :
    inner ℝ (operator J f) g = inner ℝ (J.adjoint f) (J.adjoint g) :=
  (J.adjoint_inner_right (J.adjoint f) g).symm

theorem inner_operator_right (J : V →L[ℝ] H) (f g : H) :
    inner ℝ f (operator J g) = inner ℝ (J.adjoint f) (J.adjoint g) :=
  (J.adjoint_inner_left (J.adjoint g) f).symm

theorem operator_isSymmetric (J : V →L[ℝ] H) : (operator J).IsSymmetric := by
  intro f g
  change inner ℝ (operator J f) g = inner ℝ f (operator J g)
  rw [inner_operator_left, inner_operator_right]

theorem inner_operator_eq_norm_sq (J : V →L[ℝ] H) (f : H) :
    inner ℝ f (operator J f) = ‖J.adjoint f‖ ^ 2 := by
  rw [inner_operator_right, real_inner_self_eq_norm_sq]

theorem inner_operator_nonneg (J : V →L[ℝ] H) (f : H) :
    0 ≤ inner ℝ f (operator J f) := by
  rw [inner_operator_eq_norm_sq]
  positivity

theorem norm_operator (J : V →L[ℝ] H) : ‖operator J‖ = ‖J‖ ^ 2 := by
  simpa only [operator, solution, ContinuousLinearMap.adjoint_adjoint,
    LinearIsometryEquiv.norm_map, pow_two] using
      ContinuousLinearMap.norm_adjoint_comp_self J.adjoint

theorem norm_operator_le_one (J : V →L[ℝ] H) (hJ : ‖J‖ ≤ 1) :
    ‖operator J‖ ≤ 1 := by
  rw [norm_operator]
  nlinarith [norm_nonneg J]

theorem adjoint_injective (J : V →L[ℝ] H) (hJ : DenseRange J) :
    Function.Injective J.adjoint := by
  intro f g hfg
  have heq : (fun y : H => inner ℝ y f) = (fun y : H => inner ℝ y g) := by
    apply hJ.equalizer (continuous_id.inner continuous_const)
      (continuous_id.inner continuous_const)
    funext v
    change inner ℝ (J v) f = inner ℝ (J v) g
    rw [← J.adjoint_inner_right, ← J.adjoint_inner_right, hfg]
  exact ext_inner_left ℝ (congrFun heq)

theorem operator_injective (J : V →L[ℝ] H) (hJ : DenseRange J) :
    Function.Injective (operator J) :=
  J.self_comp_adjoint_injective_iff.mpr (adjoint_injective J hJ)

theorem inner_operator_pos (J : V →L[ℝ] H) (hJ : DenseRange J)
    (f : H) (hf : f ≠ 0) : 0 < inner ℝ f (operator J f) := by
  rw [inner_operator_right]
  apply real_inner_self_pos.mpr
  intro hzero
  exact hf (adjoint_injective J hJ (by simpa using hzero))

theorem operator_compact (J : V →L[ℝ] H) (hJ : IsCompactOperator J) :
    IsCompactOperator (operator J) := hJ.comp_clm J.adjoint

theorem eigenvalue_pos (J : V →L[ℝ] H) (hJ : DenseRange J)
    {f : H} (hf : f ≠ 0) {mu : ℝ} (heig : operator J f = mu • f) : 0 < mu := by
  have hp := inner_operator_pos J hJ f hf
  rw [heig, inner_smul_right, real_inner_self_eq_norm_sq] at hp
  exact (mul_pos_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hf))).mp hp

theorem eigenvalue_le_one (J : V →L[ℝ] H) (hJ : DenseRange J)
    (hnorm : ‖J‖ ≤ 1) {f : H} (hf : f ≠ 0) {mu : ℝ}
    (heig : operator J f = mu • f) : mu ≤ 1 := by
  have hmu := eigenvalue_pos J hJ hf heig
  have hbound : ‖operator J f‖ ≤ 1 * ‖f‖ :=
    ((operator J).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (norm_operator_le_one J hnorm) (norm_nonneg f))
  rw [heig, norm_smul, Real.norm_eq_abs, abs_of_pos hmu] at hbound
  nlinarith [norm_pos_iff.mpr hf]


def parameter (mu : ℝ) (hmu : 0 < mu) (hle : mu ≤ 1) : NNReal :=
  ⟨mu⁻¹ - 1, by
    have hinv := inv_nonneg.mpr hmu.le
    have hmul := mul_inv_cancel₀ hmu.ne'
    have hle' := mul_le_mul_of_nonneg_right hle hinv
    nlinarith⟩

@[simp] theorem parameter_coe (mu : ℝ) (hmu : 0 < mu) (hle : mu ≤ 1) :
    (parameter mu hmu hle : ℝ) = mu⁻¹ - 1 := rfl

theorem parameter_resolvent_identity (mu : ℝ) (hmu : 0 < mu) (hle : mu ≤ 1) :
    (1 + (parameter mu hmu hle : ℝ)) * mu = 1 := by
  simp only [parameter_coe]
  field_simp
  ring

theorem eigenspaces_total (J : V →L[ℝ] H) (hJ : IsCompactOperator J) :
    (⨆ mu : ℝ, Module.End.eigenspace (operator J).toLinearMap mu)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (operator_compact J hJ) (operator_isSymmetric J)

theorem eigenspace_finiteDimensional (J : V →L[ℝ] H) (hJ : IsCompactOperator J)
    (mu : ℝ) (hmu : mu ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace (operator J).toLinearMap mu) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (operator_compact J hJ) mu hmu

end PoincareConjecture.HilbertResolventNative
