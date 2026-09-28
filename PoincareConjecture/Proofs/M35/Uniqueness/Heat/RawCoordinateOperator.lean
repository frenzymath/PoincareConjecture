import PoincareConjecture.Proofs.M35.Uniqueness.KillingBochner
import PoincareConjecture.Proofs.M03.Existence.CoordinateEllipticityNative
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Curvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def rawConnectionCoefficient {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (x : V) : V →L[ℝ] V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap {
    toFun := fun u => LinearMap.toContinuousLinearMap {
      toFun := fun v => D.euclideanConnection u v x
      map_add' := fun v w => congrFun (D.euclideanConnection_add_right u v w) x
      map_smul' := fun c v => congrFun (D.euclideanConnection_smul_right c u v) x }
    map_add' := fun u v => by
      apply ContinuousLinearMap.ext
      intro w
      exact congrFun (D.euclideanConnection_add_left u v w) x
    map_smul' := fun c u => by
      apply ContinuousLinearMap.ext
      intro w
      exact congrFun (D.euclideanConnection_smul_left c u w) x }

theorem rawConnectionCoefficient_contDiff {g : RiemannianMetric n V}
    (D : LeviCivitaData g) : ContDiff ℝ ∞ (rawConnectionCoefficient D) := by
  apply contDiff_clm_apply_iff.mpr
  intro u
  apply contDiff_clm_apply_iff.mpr
  intro v
  exact contDiff_iff_contDiffAt.mpr fun x => D.contDiffAt_euclideanConnection x u v

theorem raw_connection_expansion {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {X : V → V} {x : V} (hX : DifferentiableAt ℝ X x) (u : V) :
    D.connection X x u = fderiv ℝ X x u + rawConnectionCoefficient D x u (X x) :=
  D.connection_eq_fderiv_add hX u

private theorem raw_connection_field_eq {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X : V → V} (hX : ContDiff ℝ ∞ X) (v : V) :
    (fun y => D.connection X y v) =
      (fun y => fderiv ℝ X y v + rawConnectionCoefficient D y v (X y)) := by
  funext y
  exact raw_connection_expansion D (hX.differentiable (by simp) y) v

theorem raw_connection_field_contDiff {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X : V → V} (hX : ContDiff ℝ ∞ X) (v : V) :
    ContDiff ℝ ∞ (fun y => D.connection X y v) := by
  rw [raw_connection_field_eq D hX v]
  exact ((hX.fderiv_right (by simp)).clm_apply contDiff_const).add
    (((rawConnectionCoefficient_contDiff D).clm_apply contDiff_const).clm_apply hX)

theorem fieldHessian_coordinate_expansion {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X : V → V} (hX : ContDiff ℝ ∞ X) (x u v : V) :
    fieldHessian D X x u v =
      fderiv ℝ (fderiv ℝ X) x u v +
      rawConnectionCoefficient D x v (fderiv ℝ X x u) +
      rawConnectionCoefficient D x u (fderiv ℝ X x v) -
      fderiv ℝ X x (rawConnectionCoefficient D x u v) +
      fderiv ℝ (rawConnectionCoefficient D) x u v (X x) +
      rawConnectionCoefficient D x u (rawConnectionCoefficient D x v (X x)) -
      rawConnectionCoefficient D x (rawConnectionCoefficient D x u v) (X x) := by
  have hX' := hX.differentiable (by simp) x
  have hdX := (hX.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiable
    (by simp) x
  have hC := (rawConnectionCoefficient_contDiff D).differentiable (by simp) x
  have hd : fderiv ℝ (fun y => D.connection X y v) x u =
      fderiv ℝ (fderiv ℝ X) x u v +
        rawConnectionCoefficient D x v (fderiv ℝ X x u) +
        fderiv ℝ (rawConnectionCoefficient D) x u v (X x) := by
    rw [raw_connection_field_eq D hX v,
      fderiv_fun_add (hdX.clm_apply (differentiableAt_const v))
        ((hC.clm_apply (differentiableAt_const v)).clm_apply hX'),
      fderiv_clm_apply hdX (differentiableAt_const v),
      fderiv_clm_apply (hC.clm_apply (differentiableAt_const v)) hX',
      fderiv_clm_apply hC (differentiableAt_const v)]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      fderiv_const_apply, zero_apply, map_zero, zero_add]
    abel
  unfold fieldHessian
  rw [raw_connection_expansion D
      ((raw_connection_field_contDiff D hX v).differentiable (by simp) x), hd]
  change _ - D.connection X x (rawConnectionCoefficient D x u v) = _
  rw [raw_connection_expansion D hX', raw_connection_expansion D hX']
  simp only [map_add]
  abel

end PoincareConjecture.M35.Uniqueness.Heat
