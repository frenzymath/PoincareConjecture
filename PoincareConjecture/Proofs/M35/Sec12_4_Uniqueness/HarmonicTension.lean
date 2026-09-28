import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCoordinateOperator
import PoincareConjecture.Proofs.M03.Existence.IntrinsicDeTurckNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.Uniqueness

open Heat DeTurckNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def mapCovariantHessian {g b : RiemannianMetric n V}
    (D : LeviCivitaData g) (B : LeviCivitaData b) (F : V → V) (x : V) :
    V →L[ℝ] V →L[ℝ] V :=
  fderiv ℝ (fderiv ℝ F) x +
    (rawConnectionCoefficient B (F x)).bilinearComp (fderiv ℝ F x) (fderiv ℝ F x) -
    (ContinuousLinearMap.compL ℝ V V V (fderiv ℝ F x)).comp
      (rawConnectionCoefficient D x)

theorem mapCovariantHessian_apply {g b : RiemannianMetric n V}
    (D : LeviCivitaData g) (B : LeviCivitaData b) (F : V → V) (x u v : V) :
    mapCovariantHessian D B F x u v =
      fderiv ℝ (fderiv ℝ F) x u v +
        B.euclideanConnection (fderiv ℝ F x u) (fderiv ℝ F x v) (F x) -
        fderiv ℝ F x (D.euclideanConnection u v x) := rfl

def mapTension {g b : RiemannianMetric n V}
    (D : LeviCivitaData g) (B : LeviCivitaData b) (F : V → V) (x : V) : V :=
  ∑ i, mapCovariantHessian D B F x (g.orthonormalBasis x i) (g.orthonormalBasis x i)

theorem connectionDifference_euclidean {g b : RiemannianMetric n V}
    (D : LeviCivitaData g) (B : LeviCivitaData b) (x u v : V) :
    CovariantDerivative.difference D.connection B.connection x v u =
      D.euclideanConnection u v x - B.euclideanConnection u v x := by
  have hv : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V))
      (fun y : V => (⟨y, v⟩ : TangentBundle (𝓡 n) V)) x := by
    rw [mdifferentiableAt_totalSpace]
    exact ⟨mdifferentiableAt_id, by simpa using mdifferentiableAt_const (c := v)⟩
  exact connectionDifference_apply_field D B hv u

theorem mapTension_id {g b : RiemannianMetric n V}
    (D : LeviCivitaData g) (B : LeviCivitaData b) (x : V) :
    mapTension D B id x = -intrinsicDeTurckField D B x := by
  have hd : fderiv ℝ (id : V → V) = fun _ => ContinuousLinearMap.id ℝ V :=
    funext fun y => fderiv_id
  unfold mapTension intrinsicDeTurckField
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mapCovariantHessian_apply, connectionDifference_euclidean]
  simp only [hd, fderiv_const_apply, zero_apply,
    ContinuousLinearMap.id_apply, id_eq, zero_add, neg_sub]

theorem mapTension_eq_inverse_gram {g b : RiemannianMetric n V}
    (D : LeviCivitaData g) (B : LeviCivitaData b) (F : V → V) (x : V)
    (e : Module.Basis (Fin n) ℝ V) :
    mapTension D B F x =
      ∑ i, ∑ j, (Matrix.of (fun i j => g.inner x (e i) (e j)))⁻¹ i j •
        mapCovariantHessian D B F x (e i) (e j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : V → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact orthonormal_trace_eq_inverse_gram (g.orthonormalBasis x) e
    (mapCovariantHessian D B F x)

end PoincareConjecture.M35.Uniqueness
