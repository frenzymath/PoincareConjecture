import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerThreePins
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerRotation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerCrosscutBoundary











set_option autoImplicit false

noncomputable section

open Set Metric Complex
open scoped Topology

namespace PoincareConjecture

private def m65ComplexLoopCircle : Circle ≃ₜ LoopCircle where
  toFun z := ⟨orthonormalBasisOneI.repr z, by rw [LinearIsometryEquiv.norm_map, z.norm_coe]⟩
  invFun z := ⟨orthonormalBasisOneI.repr.symm z,
    mem_sphere_zero_iff_norm.mpr (by rw [LinearIsometryEquiv.norm_map, z.property])⟩
  left_inv z := Subtype.ext (orthonormalBasisOneI.repr.symm_apply_apply z)
  right_inv z := Subtype.ext (orthonormalBasisOneI.repr.apply_symm_apply z)
  continuous_toFun := (orthonormalBasisOneI.repr.continuous.comp continuous_subtype_val).subtype_mk
    (fun z => by
      change ‖orthonormalBasisOneI.repr (z : ℂ)‖ = 1
      rw [LinearIsometryEquiv.norm_map]
      exact mem_sphere_zero_iff_norm.mp z.property)
  continuous_invFun :=
    (orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val).subtype_mk
    (fun z => mem_sphere_zero_iff_norm.mpr (by
      change ‖orthonormalBasisOneI.repr.symm (z : LoopPlane)‖ = 1
      rw [LinearIsometryEquiv.norm_map, z.property]))



def m65LoopAngular (t : ℝ) : LoopCircle :=
  ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩

private theorem m65LoopAngular_eq (t : ℝ) :
    m65LoopAngular t = m65ComplexLoopCircle (Circle.exp t) := by
  apply Subtype.ext
  change Proofs.M58.angularPoint t = orthonormalBasisOneI.repr (Circle.exp t : ℂ)
  ext i
  fin_cases i <;> simp [Proofs.M58.angularPoint,
    Circle.coe_exp, Complex.exp_mul_I, orthonormalBasisOneI_repr_apply,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]



theorem m65LoopAngular_open : IsOpenMap m65LoopAngular := by
  have he : m65LoopAngular = m65ComplexLoopCircle ∘ Circle.exp := funext m65LoopAngular_eq
  rw [he]
  exact m65ComplexLoopCircle.isOpenMap.comp isLocalHomeomorph_circleExp.isOpenMap



theorem m65LoopAngular_continuous_surjective :
    Continuous m65LoopAngular ∧ Function.Surjective m65LoopAngular := by
  have he : m65LoopAngular = m65ComplexLoopCircle ∘ Circle.exp := funext m65LoopAngular_eq
  rw [he]
  refine ⟨m65ComplexLoopCircle.continuous.comp Circle.exp.continuous, ?_⟩
  intro z
  refine ⟨Complex.arg (m65ComplexLoopCircle.symm z), ?_⟩
  simp only [Function.comp_apply, Circle.exp_arg, Homeomorph.apply_symm_apply]



def m65CrosscutBoundaryWidth (r : ℝ) : ℝ := Real.pi - 2 * m65CrosscutAngle r



theorem m65CrosscutBoundaryWidth_bounds {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    0 < m65CrosscutBoundaryWidth r ∧ m65CrosscutBoundaryWidth r < Real.pi := by
  have h0 := Real.arccos_pos.mpr (show r / 2 < 1 by linarith)
  have h1 := Real.arccos_lt_pi_div_two.mpr (show 0 < r / 2 by positivity)
  dsimp only [m65CrosscutBoundaryWidth, m65CrosscutAngle]
  constructor <;> linarith



theorem m65CrosscutBoundaryWidth_mono : Monotone m65CrosscutBoundaryWidth := by
  intro r s hrs
  have h := Real.arccos_le_arccos (show r / 2 ≤ s / 2 by linarith)
  dsimp only [m65CrosscutBoundaryWidth, m65CrosscutAngle]
  linarith




theorem m65CrosscutBoundaryArc_endpoints (θ : ℝ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    let d := m65CrosscutBoundaryWidth r
    let s := fun t => m65LoopAngular (θ + Real.pi + t)
    Continuous s ∧ InjOn s (Icc (-d) d) ∧
      s (-d) = m65LoopAngular (θ + 2 * m65CrosscutAngle r) ∧
      s d = m65LoopAngular (θ - 2 * m65CrosscutAngle r) := by
  dsimp only
  refine ⟨m65LoopAngular_continuous_surjective.1.comp
    (continuous_const.add continuous_id), ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    change m65LoopAngular (θ + Real.pi + x) = m65LoopAngular (θ + Real.pi + y) at hxy
    have hi := Circle.exp_injOn_Icc (a := θ + Real.pi - m65CrosscutBoundaryWidth r)
      (b := θ + Real.pi + m65CrosscutBoundaryWidth r)
      (by linarith [(m65CrosscutBoundaryWidth_bounds hr hr1).2])
    rw [m65LoopAngular_eq, m65LoopAngular_eq] at hxy
    have he := hi (show θ + Real.pi + x ∈ Icc
        (θ + Real.pi - m65CrosscutBoundaryWidth r)
        (θ + Real.pi + m65CrosscutBoundaryWidth r) by constructor <;> linarith [hx.1, hx.2])
      (show θ + Real.pi + y ∈ Icc
        (θ + Real.pi - m65CrosscutBoundaryWidth r)
        (θ + Real.pi + m65CrosscutBoundaryWidth r) by constructor <;> linarith [hy.1, hy.2])
      (m65ComplexLoopCircle.injective hxy)
    linarith
  · congr 1
    dsimp only [m65CrosscutBoundaryWidth]
    ring
  · have he : θ + Real.pi + m65CrosscutBoundaryWidth r =
        (θ - 2 * m65CrosscutAngle r) + 2 * Real.pi := by
      dsimp only [m65CrosscutBoundaryWidth]
      ring
    rw [he, m65LoopAngular_eq, m65LoopAngular_eq, Circle.exp_add_two_pi]





theorem m65CrosscutBoundaryArc_dist_center (θ : ℝ) {r t : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (ht : t ∈ Icc (-m65CrosscutBoundaryWidth r) (m65CrosscutBoundaryWidth r)) :
    dist (m65LoopAngular (θ + Real.pi + t)) (m65LoopAngular (θ + Real.pi)) ≤ r := by
  have hcenter : Proofs.M58.angularPoint (θ + Real.pi) =
      m65PlaneRotation (θ + Real.pi) (Proofs.M58.angularPoint 0) := by
    rw [m65PlaneRotation_angular, add_zero]
  change dist (Proofs.M58.angularPoint (θ + Real.pi + t))
    (Proofs.M58.angularPoint (θ + Real.pi)) ≤ r
  rw [← m65PlaneRotation_angular, hcenter, LinearIsometryEquiv.dist_map, dist_eq_norm]
  have hdpi := (m65CrosscutBoundaryWidth_bounds hr hr1).2.le
  have hct := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t) hdpi (abs_le.mpr ht)
  have hcos : Real.cos (m65CrosscutBoundaryWidth r) = 1 - r ^ 2 / 2 := by
    rw [m65CrosscutBoundaryWidth, Real.cos_pi_sub, Real.cos_two_mul,
      show Real.cos (m65CrosscutAngle r) = r / 2 from Real.cos_arccos (by linarith) (by linarith)]
    ring
  rw [Real.cos_abs, hcos] at hct
  apply (sq_le_sq₀ (norm_nonneg _) hr.le).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, Proofs.M58.angularPoint,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.cos_zero,
    Real.sin_zero, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq t]

end PoincareConjecture
