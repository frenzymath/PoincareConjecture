import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Uniqueness.Heat.RawCoordinateOperator
import PoincareLib.Geometry.RicciFlow.Local.DeTurck.Construction.IntrinsicDeTurck

/-!
# The actual harmonic-map Hessian and tension

Morgan-Tian Section 12.6, pp. 307-322, with the radial-gauge erratum.
The Hessian below uses the ordinary differential and both retained
Levi-Civita connections. Its trace is the genuine map tension. In
particular, the identity map has tension equal to minus the native
DeTurck field, fixing the sign consumed by the gauge comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.M35.Uniqueness

open Heat DeTurckNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

/-- The covariant Hessian of a map, using the actual source and target
connections. The last term differentiates the source arguments. -/
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

/-- The source metric trace of the genuine map Hessian. -/
def mapTension {g b : RiemannianMetric n V}
    (D : LeviCivitaData g) (B : LeviCivitaData b) (F : V → V) (x : V) : V :=
  ∑ i, mapCovariantHessian D B F x (g.orthonormalBasis x i) (g.orthonormalBasis x i)

/-- Constant fields identify the actual connection difference in the
Euclidean presentation; no new connection is selected. -/
theorem connectionDifference_euclidean {g b : RiemannianMetric n V}
    (D : LeviCivitaData g) (B : LeviCivitaData b) (x u v : V) :
    CovariantDerivative.difference D.connection B.connection x v u =
      D.euclideanConnection u v x - B.euclideanConnection u v x := by
  have hv : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V))
      (fun y : V => (⟨y, v⟩ : TangentBundle (𝓡 n) V)) x := by
    rw [mdifferentiableAt_totalSpace]
    exact ⟨mdifferentiableAt_id, by simpa using mdifferentiableAt_const (c := v)⟩
  exact connectionDifference_apply_field D B hv u

/-- The identity's harmonic tension is exactly the negative of the
existing native DeTurck vector. -/
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

/-- The map tension can be traced in any genuine basis with its actual
source inverse Gram matrix. -/
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

end PoincareMT.M35.Uniqueness
