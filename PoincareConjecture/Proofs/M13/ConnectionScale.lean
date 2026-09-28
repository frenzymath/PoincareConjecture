import PoincareConjecture.Proofs.M13.Metric
import PoincareConjecture.Proofs.Ch01.Koszul









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


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
  rw [mvfderiv_const_mul_metric_inner g Q Y Z x hY hZ, D.mvfderiv_inner X Y Z hY hZ]
  ring


noncomputable def scaleLeviCivitaData (D : LeviCivitaData g) (Q : ℝ) (hQ : 0 < Q) :
    LeviCivitaData (scaleSmoothMetric g Q hQ) where
  connection := D.connection
  smooth := D.smooth
  torsion_eq_zero := D.torsion_eq_zero
  metricCompatible := metricCompatible_of_inner_eq D _ Q (fun _ _ _ ↦ rfl)


theorem scaleLeviCivitaData_connection (D : LeviCivitaData g) (Q : ℝ) (hQ : 0 < Q) :
    (scaleLeviCivitaData D Q hQ).connection = D.connection := rfl


theorem scale_connection_eq_at (D : LeviCivitaData g) (Q : ℝ) (hQ : 0 < Q)
    (D' : LeviCivitaData (scaleSmoothMetric g Q hQ))
    (Y : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x) :
    D'.connection Y x = D.connection Y x :=
  D'.connection_eq_at (scaleLeviCivitaData D Q hQ) Y hY

end PoincareConjecture.M13
