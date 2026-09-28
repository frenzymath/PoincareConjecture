import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryModulus
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicArclength













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace PoincareConjecture.M64Uniformization





theorem exists_scalar_degree_one_boundary_inverse
    {v : ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hperiod : Function.Periodic v curvePeriod)
    (hpos : ∀ x, 0 < v x) :
    ∃ φ : ℝ ≃ₜ ℝ,
      (∀ x, φ (x + curvePeriod) = φ x + curvePeriod) ∧
      (∀ y, φ.symm (y + curvePeriod) = φ.symm y + curvePeriod) ∧
      (∀ x, 0 < deriv (φ : ℝ → ℝ) x) ∧
      (∀ y, 0 < deriv (φ.symm : ℝ → ℝ) y) := by
  have hperiod_pos : 0 < curvePeriod := by
    unfold curvePeriod
    positivity
  obtain ⟨-, φ, -, -, -, -, hshift, hinvshift, hder, hderinv⟩ :=
    PoincareConjecture.M63.exists_periodic_arclength_homeomorph hperiod_pos hv hperiod hpos
  refine ⟨φ, hshift, hinvshift, ?_, ?_⟩
  · intro x
    exact (hder x).2
  · intro y
    exact (hderinv y).2






theorem exists_scalar_periodic_degree_one_lift
    {v : ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hperiod : Function.Periodic v curvePeriod)
    (hpos : ∀ x, 0 < v x) :
    ∃ σ : M64PeriodicDegreeOneLift,
      ∃ φ : ℝ ≃ₜ ℝ,
        σ.map = φ ∧
        (∀ x, φ (x + curvePeriod) = φ x + curvePeriod) ∧
        (∀ y, φ.symm (y + curvePeriod) = φ.symm y + curvePeriod) ∧
        (∀ x, 0 < deriv (φ : ℝ → ℝ) x) ∧
        (∀ y, 0 < deriv (φ.symm : ℝ → ℝ) y) := by
  have hperiod_pos : 0 < curvePeriod := by
    unfold curvePeriod
    positivity
  obtain ⟨hell, φ, hformula, hφ, hφi, hzero, hshift, hinvshift, hder, hderinv⟩ :=
    PoincareConjecture.M63.exists_periodic_arclength_homeomorph hperiod_pos hv hperiod hpos
  have hderiv_formula (x : ℝ) :
      deriv (φ : ℝ → ℝ) x = (curvePeriod / (∫ y in (0 : ℝ)..curvePeriod, v y)) * v x :=
    (hder x).1.deriv
  have hderiv_period : Function.Periodic (fun x => deriv (φ : ℝ → ℝ) x) curvePeriod := by
    intro x
    change deriv (φ : ℝ → ℝ) (x + curvePeriod) = deriv (φ : ℝ → ℝ) x
    rw [hderiv_formula, hderiv_formula, hperiod x]
  have hderiv_cont : Continuous (fun x => deriv (φ : ℝ → ℝ) x) :=
    hφ.continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ :=
    (hderiv_period.compact_of_continuous hperiod_pos.ne' hderiv_cont).exists_bound_of_continuousOn
      continuousOn_id
  let C' : ℝ := max 0 C
  have hC' : 0 ≤ max (0 : ℝ) C := le_max_left _ _
  let Cnn : ℝ≥0 := ⟨max (0 : ℝ) C, hC'⟩
  have hCnn : (Cnn : ℝ) = C' := by
    rfl
  have hbound (x : ℝ) : ‖deriv (φ : ℝ → ℝ) x‖₊ ≤ Cnn := by
    apply_mod_cast (show ‖deriv (φ : ℝ → ℝ) x‖ ≤ C' by
      exact (hC _ ⟨x, rfl⟩).trans (le_max_right _ _))
  have hLip : LipschitzWith Cnn (φ : ℝ → ℝ) :=
    lipschitzWith_of_nnnorm_deriv_le
      (hφ.differentiable (by norm_num)) (fun x => hbound x)
  let σ : M64PeriodicDegreeOneLift :=
    { map := φ
      monotone := (strictMono_of_hasDerivAt_pos
        (fun x => (hder x).1)
        (fun x => by rw [← hderiv_formula]; exact (hder x).2)).monotone
      period_shift := hshift
      lipschitz_constant := C'
      lipschitz_nonnegative := le_max_left _ _
      lipschitz_on := by
        intro x y
        have hxy := hLip.dist_le_mul x y
        simpa only [Real.dist_eq, abs_sub_comm, hCnn] using hxy }
  refine ⟨σ, φ, ?_, hshift, hinvshift, ?_, ?_⟩
  · rfl
  · intro x
    exact (hder x).2
  · intro y
    exact (hderinv y).2

end PoincareConjecture.M64Uniformization
