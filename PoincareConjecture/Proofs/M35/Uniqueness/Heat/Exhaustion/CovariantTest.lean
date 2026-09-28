import PoincareConjecture.Proofs.M35.Uniqueness.KillingDefectTensor
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCoordinateOperator
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem smooth_twoTensor_pair_contDiff
    {H : V → (Fin 2 → V) → ℝ} (hH : IsSmoothCovariantTensor H)
    {U W : V → V} (hU : ContDiff ℝ ∞ U) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (fun x => H x ![U x, W x]) := by
  have hfields (i : Fin 2) : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x => Bundle.TotalSpace.mk' V x (E := TangentSpace (𝓡 n)) (![U, W] i x)) univ := by
    fin_cases i
    · exact (euclidean_field_contMDiff hU).contMDiffOn
    · exact (euclidean_field_contMDiff hW).contMDiffOn
  have hh := hH.2 univ isOpen_univ ![U, W] hfields
  have he : (fun x => H x (fun i => ![U, W] i x)) = fun x => H x ![U x, W x] := by
    funext x
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [he] at hh
  exact contDiffOn_univ.mp hh.contDiffOn

theorem covariant_twoTensor_derivative_coordinates
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {H : V → (Fin 2 → V) → ℝ} (hH : IsSmoothCovariantTensor H)
    (x u v w : V) :
    D.covariantTensorDerivative H x ![u, v, w] =
      fderiv ℝ (fun y => H y ![v, w]) x u -
        H x ![rawConnectionCoefficient D x u v, w] -
        H x ![v, rawConnectionCoefficient D x u w] := by
  have hC (a : V) := euclidean_field_contMDiff
    (contDiff_const (c := a) : ContDiff ℝ ∞ (fun _ : V => a))
  have he := M04.covariantTensorDerivativeOnFields_eq D hH isOpen_univ
    (X := fun i _ => (![u, v, w] : Fin 3 → V) i)
    (fun i => (hC _).contMDiffOn) (x := x) (mem_univ x)
  rw [← he]
  simp only [M04.covariantTensorDerivativeOnFields, Fin.sum_univ_two, Matrix.cons_val_zero]
  have ht : (fun i : Fin 2 => (![u, v, w] : Fin 3 → V) i.succ) = ![v, w] := rfl
  rw [ht]
  simp only [mvfderiv, mfderiv_eq_fderiv]
  have hv (a : V) : Function.update ![v, w] (0 : Fin 2) a = ![a, w] := by
    ext i
    fin_cases i <;> simp
  have hw (a : V) : Function.update ![v, w] (1 : Fin 2) a = ![v, a] := by
    ext i
    fin_cases i <;> simp
  change fderiv ℝ (fun y => H y ![v, w]) x u -
    (H x (Function.update ![v, w] 0 (rawConnectionCoefficient D x u v)) +
      H x (Function.update ![v, w] 1 (rawConnectionCoefficient D x u w))) = _
  rw [hv, hw]
  ring

theorem integral_mul_covariant_twoTensor_derivative
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {H : V → (Fin 2 → V) → ℝ} (hH : IsSmoothCovariantTensor H)
    {a : V → ℝ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (u v w : V) :
    (∫ x, a x * D.covariantTensorDerivative H x ![u, v, w]) =
      -(∫ x, fderiv ℝ a x u * H x ![v, w]) -
        (∫ x, a x * H x ![rawConnectionCoefficient D x u v, w]) -
        (∫ x, a x * H x ![v, rawConnectionCoefficient D x u w]) := by
  have hpair : ContDiff ℝ ∞ (fun x => H x ![v, w]) :=
    smooth_twoTensor_pair_contDiff hH contDiff_const contDiff_const
  have hΓv : ContDiff ℝ ∞ (fun x => rawConnectionCoefficient D x u v) :=
    ((rawConnectionCoefficient_contDiff D).clm_apply contDiff_const).clm_apply contDiff_const
  have hΓw : ContDiff ℝ ∞ (fun x => rawConnectionCoefficient D x u w) :=
    ((rawConnectionCoefficient_contDiff D).clm_apply contDiff_const).clm_apply contDiff_const
  have hleft : Integrable (fun x => a x * fderiv ℝ (fun y => H y ![v, w]) x u) :=
    (ha.continuous.mul ((hpair.continuous_fderiv (by simp)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport hac.mul_right
  have hright : Integrable (fun x => fderiv ℝ a x u * H x ![v, w]) :=
    (((ha.continuous_fderiv (by simp)).clm_apply continuous_const).mul hpair.continuous
      ).integrable_of_hasCompactSupport (hac.fderiv_apply ℝ u).mul_right
  have hprod : Integrable (fun x => a x * H x ![v, w]) :=
    (ha.continuous.mul hpair.continuous).integrable_of_hasCompactSupport hac.mul_right
  have hcv : Integrable (fun x => a x * H x ![rawConnectionCoefficient D x u v, w]) :=
    (ha.continuous.mul (smooth_twoTensor_pair_contDiff hH hΓv contDiff_const).continuous
      ).integrable_of_hasCompactSupport hac.mul_right
  have hcw : Integrable (fun x => a x * H x ![v, rawConnectionCoefficient D x u w]) :=
    (ha.continuous.mul (smooth_twoTensor_pair_contDiff hH contDiff_const hΓw).continuous
      ).integrable_of_hasCompactSupport hac.mul_right
  have hip := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hright hleft hprod
    (fun x _ => ha.differentiable (by simp) x) (fun x _ => hpair.differentiable (by simp) x)
  have hsub := integral_sub (hleft.sub hcv) hcw
  have hsub' := integral_sub hleft hcv
  simp only [Pi.sub_apply] at hsub hsub'
  simp only [covariant_twoTensor_derivative_coordinates D hH, mul_sub]
  rw [hsub, hsub', hip]

theorem covariant_twoTensor_fixed_contDiff
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {H : V → (Fin 2 → V) → ℝ} (hH : IsSmoothCovariantTensor H) (u v w : V) :
    ContDiff ℝ ∞ (fun x => D.covariantTensorDerivative H x ![u, v, w]) := by
  have hS := M04.isSmoothCovariantTensor_covariantTensorDerivative D hH
  have hc (z : V) := (euclidean_field_contMDiff
    (contDiff_const (c := z) : ContDiff ℝ ∞ (fun _ : V => z))).contMDiffOn (s := univ)
  exact contDiffOn_univ.mp (hS.2 univ isOpen_univ
    (fun i _ => (![u, v, w] : Fin 3 → V) i) (fun i => hc _)).contDiffOn

end PoincareConjecture.M35.Uniqueness.Heat
