import PoincareLib.Geometry.Riemannian.Homothety.Metric
import PoincareLib.Geometry.Riemannian.Normalization.Connection.Koszul

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M13/ConnectionScale.lean`,
revision `0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See `references/ricci-flow/mapher/rescaling-import.json`. -/

/-!
# Levi-Civita data under constant positive metric scaling

The connection itself is retained. Metric compatibility follows by
differentiating the constant multiple of the original metric, as in
Morgan-Tian Theorem 1.2 and Definition 3.40, pp. 3-4 and 61.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.Homothety

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Inner products of differentiable fields use the explicitly selected metric. -/
theorem metric_inner_mdifferentiableAt (g : RiemannianMetric n M)
    (Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) x) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ) (fun p ↦ g.inner p (Y p) (Z p)) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact hY.inner_bundle hZ

/-- Differentiating a constant multiple of the metric pairing. -/
theorem mvfderiv_const_mul_metric_inner (g : RiemannianMetric n M) (Q : ℝ)
    (Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) x) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun p ↦ Q * g.inner p (Y p) (Z p)) x v =
      Q * mvfderiv (𝓡 n) (fun p ↦ g.inner p (Y p) (Z p)) x v := by
  rw [mvfderiv_fun_mul mdifferentiableAt_const (metric_inner_mdifferentiableAt g Y Z x hY hZ)]
  simp only [mvfderiv_const, smul_zero, add_zero, smul_apply, smul_eq_mul]

/-- Constant multiplication preserves compatibility of the chosen connection. -/
theorem metricCompatible_of_inner_eq (D : LeviCivitaData g)
    (h : RiemannianMetric n M) (Q : ℝ)
    (hscale : ∀ x (u v : TangentSpace (𝓡 n) x),
      h.inner x u v = Q * g.inner x u v) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨h.toRiemannianMetric⟩
    D.connection.IsMetricCompatible := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨h.toRiemannianMetric⟩
  apply (CovariantDerivative.isMetricCompatible_iff D.connection).2
  intro x X Y Z _hX hY hZ
  change mvfderiv (𝓡 n) (fun p ↦ h.inner p (Y p) (Z p)) x (X x) =
    h.inner x (D.connection Y x (X x)) (Z x) +
      h.inner x (Y x) (D.connection Z x (X x))
  simp_rw [hscale]
  rw [mvfderiv_const_mul_metric_inner g Q Y Z x hY hZ, D.normalization_mvfderiv_inner X Y Z hY hZ]
  ring

/-- A constant positive metric multiple has the same chosen connection. -/
noncomputable def scaleLeviCivitaData (D : LeviCivitaData g) (Q : ℝ) (hQ : 0 < Q) :
    LeviCivitaData (scaleSmoothMetric g Q hQ) where
  connection := D.connection
  smooth := D.smooth
  torsion_eq_zero := D.torsion_eq_zero
  metricCompatible := metricCompatible_of_inner_eq D _ Q (fun _ _ _ ↦ rfl)

/-- The construction retains the original section operator exactly. -/
theorem scaleLeviCivitaData_connection (D : LeviCivitaData g) (Q : ℝ) (hQ : 0 < Q) :
    (scaleLeviCivitaData D Q hQ).connection = D.connection := rfl

/-- Any other compatible torsion-free connection agrees on regular sections. -/
theorem scale_connection_eq_at (D : LeviCivitaData g) (Q : ℝ) (hQ : 0 < Q)
    (D' : LeviCivitaData (scaleSmoothMetric g Q hQ))
    (Y : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x) :
    D'.connection Y x = D.connection Y x :=
  D'.normalization_connection_eq_at (scaleLeviCivitaData D Q hQ) Y hY

end PoincareMT.Homothety
