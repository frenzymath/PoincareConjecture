import PoincareConjecture.Proofs.M36.CylinderCoefficientField
import Mathlib.Analysis.Calculus.ContDiff.Bounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "C" => RoundCylinderCoordinates

noncomputable def centeredCylinderComponent (B : RoundCylinderTwoTensor)
    (theta : UnitTwoSphere) (s : ℝ) (k : ℕ) (a : Fin (2 + k) → Fin 3) (p : E₃) : ℝ :=
  roundCylinderIteratedDerivative 0 (chartAt E₂ theta) B k
    (cylinderEuclideanEquiv p + (0, s)) a

noncomputable def centeredCylinderChristoffel (a b c : Fin 3) (p : E₃) : ℝ :=
  (-2 / (‖(cylinderEuclideanEquiv p).1‖ ^ 2 + 4)) *
    cylinderChristoffelLinear a b c (cylinderEuclideanEquiv p)

theorem centeredCylinderChristoffel_contDiff (a b c : Fin 3) :
    ContDiff ℝ ∞ (centeredCylinderChristoffel a b c) := by
  unfold centeredCylinderChristoffel
  apply ContDiff.mul
  · apply contDiff_const.div
      ((((contDiff_norm_sq ℝ).comp contDiff_fst).comp
        cylinderEuclideanEquiv.contDiff).add contDiff_const)
    intro p
    exact ne_of_gt (show 0 < ‖(cylinderEuclideanEquiv p).1‖ ^ 2 + 4 by positivity)
  · exact (cylinderChristoffelLinear a b c).contDiff.comp
      cylinderEuclideanEquiv.contDiff

theorem roundCylinderChristoffel_affine (theta : UnitTwoSphere) (s : ℝ)
    (a b c : Fin 3) (p : E₃) :
    roundCylinderChristoffel 0 (chartAt E₂ theta)
      (cylinderEuclideanEquiv p + (0, s)) a b c =
        centeredCylinderChristoffel a b c p := by
  rw [roundCylinderChristoffel_chart]
  simp [centeredCylinderChristoffel, cylinderChristoffelLinear,
    cylinderHorizontalCovector]

theorem centeredCylinderComponent_succ (B : RoundCylinderTwoTensor)
    (theta : UnitTwoSphere) (s : ℝ) (k : ℕ)
    (a : Fin (2 + (k + 1)) → Fin 3) (p : E₃) :
    centeredCylinderComponent B theta s (k + 1) a p =
      fderiv ℝ (centeredCylinderComponent B theta s k (fun l => a l.succ)) p
        (EuclideanSpace.basisFun (Fin 3) ℝ (a 0)) -
      ∑ l : Fin (2 + k), ∑ b : Fin 3,
        centeredCylinderChristoffel b (a 0) (a l.succ) p *
          centeredCylinderComponent B theta s k
            (Function.update (fun m => a m.succ) l b) p := by
  simp +unfoldPartialApp only [centeredCylinderComponent, roundCylinderIteratedDerivative,
    roundCylinderTensorDerivative, roundCylinderChristoffel_affine]
  congr 1
  have h := fderiv_cylinder_affine
    (fun q => roundCylinderIteratedDerivative 0 (chartAt E₂ theta) B k q
      (fun l => a l.succ)) (0, s) p (EuclideanSpace.basisFun (Fin 3) ℝ (a 0))
  rw [cylinderEuclideanEquiv_basis] at h
  convert! h.symm using 1

theorem centeredCylinderComponent_fderiv_basis (B : RoundCylinderTwoTensor)
    (theta : UnitTwoSphere) (s : ℝ) (k : ℕ) (a : Fin (2 + k) → Fin 3)
    (i : Fin 3) (p : E₃) :
    fderiv ℝ (centeredCylinderComponent B theta s k a) p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      centeredCylinderComponent B theta s (k + 1) (Fin.cons i a) p +
      ∑ l : Fin (2 + k), ∑ b : Fin 3,
        centeredCylinderChristoffel b i (a l) p *
          centeredCylinderComponent B theta s k (Function.update a l b) p := by
  rw [centeredCylinderComponent_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact (sub_add_cancel _ _).symm

theorem centeredCylinderComponent_contDiffAt {epsilon : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹)
    (k : ℕ) (a : Fin (2 + k) → Fin 3) :
    ContDiffAt ℝ ∞ (centeredCylinderComponent B z.1 z.2 k a) 0 := by
  induction k with
  | zero =>
      have hc := roundCylinder_metric_error_contDiffAt hB z hz a
      have ha : ContDiffAt ℝ ∞
          (fun p : E₃ => cylinderEuclideanEquiv p + (0, z.2)) 0 :=
        cylinderEuclideanEquiv.contDiff.contDiffAt.add contDiffAt_const
      have hc' : ContDiffAt ℝ ∞
          (fun p => roundCylinderIteratedDerivative 0 (chartAt E₂ z.1) B 0 p a)
          (cylinderEuclideanEquiv 0 + (0, z.2)) := by
        simpa only [map_zero, zero_add] using hc
      exact hc'.comp 0 ha
  | succ k ih =>
      simp only [show centeredCylinderComponent B z.1 z.2 (k + 1) a =
          fun p => fderiv ℝ
            (centeredCylinderComponent B z.1 z.2 k (fun l => a l.succ)) p
            (EuclideanSpace.basisFun (Fin 3) ℝ (a 0)) -
            ∑ l : Fin (2 + k), ∑ b : Fin 3,
              centeredCylinderChristoffel b (a 0) (a l.succ) p *
                centeredCylinderComponent B z.1 z.2 k
                  (Function.update (fun m => a m.succ) l b) p from
        funext (centeredCylinderComponent_succ B z.1 z.2 k a)]
      apply ContDiffAt.sub
      · exact ((ih _).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
      · apply ContDiffAt.sum
        intro l _
        apply ContDiffAt.sum
        intro b _
        exact (centeredCylinderChristoffel_contDiff b (a 0) (a l.succ)).contDiffAt.mul
          (ih _)

theorem centeredCylinderComponent_center_bound {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon 0 B)
    {k : ℕ} (hk : k ≤ ⌊epsilon⁻¹⌋₊) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹) (a : Fin (2 + k) → Fin 3) :
    ‖centeredCylinderComponent B z.1 z.2 k a 0‖ ≤
      Real.sqrt ((2 : ℝ) ^ (2 + k)) * epsilon := by
  have h := roundCylinderClose_derivative_component hepsilon hB hk z hz a
  rw [sphere_chart_center_zero] at h
  simpa only [centeredCylinderComponent, map_zero, zero_add, Real.norm_eq_abs] using h

theorem norm_iteratedFDeriv_smul_fixed {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E₃ → ℝ} {x : E₃}
    (hf : ContDiffAt ℝ ∞ f x) (v : F) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun p => f p • v) x‖ ≤
      ‖iteratedFDeriv ℝ j f x‖ * ‖v‖ := by
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.norm_toSpanSingleton, mul_comm] using
      (ContinuousLinearMap.toSpanSingleton ℝ v).norm_iteratedFDeriv_comp_left hf
        (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)

theorem norm_iteratedFDeriv_finite_sum {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]
    (f : ι → E₃ → F) {x : E₃} (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun p => ∑ i, f i p) x‖ ≤
      ∑ i, ‖iteratedFDeriv ℝ j (f i) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply
    (fun i _ => (hf i).of_le (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top))]
  exact norm_sum_le _ _

theorem euclideanThree_dual_expansion (L : E₃ →L[ℝ] ℝ) :
    L = ∑ i : Fin 3, L (EuclideanSpace.basisFun (Fin 3) ℝ i) •
      innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  apply ContinuousLinearMap.ext
  intro v
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr' v]
  simp only [map_sum, map_smul, sum_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem norm_iteratedFDeriv_succ_le_basis {f : E₃ → ℝ} {x : E₃}
    (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) :
    ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤
      ∑ i : Fin 3, ‖iteratedFDeriv ℝ j
        (fun p => fderiv ℝ f p (EuclideanSpace.basisFun (Fin 3) ℝ i)) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv]
  have heq : fderiv ℝ f = fun p => ∑ i : Fin 3,
      fderiv ℝ f p (EuclideanSpace.basisFun (Fin 3) ℝ i) •
        innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i) :=
    funext (fun p => euclideanThree_dual_expansion (fderiv ℝ f p))
  conv_lhs => rw [heq]
  have hi (i : Fin 3) : ContDiffAt ℝ ∞
      (fun p => fderiv ℝ f p (EuclideanSpace.basisFun (Fin 3) ℝ i)) x :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  apply (norm_iteratedFDeriv_finite_sum _ (fun i => (hi i).smul contDiffAt_const) j).trans
  apply Finset.sum_le_sum
  intro i _
  simpa only [Pi.smul_def', innerSL_apply_norm, (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one,
    mul_one] using
    norm_iteratedFDeriv_smul_fixed (hi i)
      (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i)) j

end PoincareConjecture.M36
