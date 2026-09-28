import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.ClosedJetEnergies
import PoincareConjecture.Proofs.M35.Uniqueness.RotationGradientBound









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem connection_eq_of_field_germ {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {X Y : V → V} {x : V} (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x)
    (he : X =ᶠ[𝓝 x] Y) (u : V) : D.connection X x u = D.connection Y x u := by
  rw [raw_connection_expansion D hX, raw_connection_expansion D hY,
    he.fderiv_eq, he.eq_of_nhds]

theorem metricLieDerivative_eq_of_field_germ {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X Y : V → V} {x : V}
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x)
    (he : X =ᶠ[𝓝 x] Y) (u v : V) :
    DeTurckNative.metricLieDerivative D X x u v =
      DeTurckNative.metricLieDerivative D Y x u v := by
  simp only [DeTurckNative.metricLieDerivative_apply,
    connection_eq_of_field_germ D hX hY he]

theorem covector_gradient_normSq_eq_of_field_germ {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X Y : V → V} {x : V}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) (he : X =ᶠ[𝓝 x] Y) :
    (g.tensorNorm (D.covariantTensorDerivative (killingCovector g X)) x) ^ 2 =
      (g.tensorNorm (D.covariantTensorDerivative (killingCovector g Y)) x) ^ 2 := by
  rw [killingCovectorGradient_normSq D X hX, killingCovectorGradient_normSq D Y hY]
  apply Finset.sum_congr rfl
  intro i _
  rw [connection_eq_of_field_germ D (hX.differentiable (by simp) x)
    (hY.differentiable (by simp) x) he]

theorem raw_initial_rotation_gradient_bound {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (hB : ∀ x, inner ℝ x (B x) = 0) (x : StandardCapSpace) :
    ((G.flow.metric 0).tensorNorm ((G.flow.connection 0).covariantTensorDerivative
      (killingCovector (G.flow.metric 0) (fun y => B y))) x) ^ 2 ≤ 9 * ‖B‖ ^ 2 := by
  have htransport (g h : RiemannianMetric 3 StandardCapSpace)
      (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h) (hD : HEq D D') :
      (g.tensorNorm (D.covariantTensorDerivative (killingCovector g (fun y => B y))) x) ^ 2 =
        (h.tensorNorm (D'.covariantTensorDerivative (killingCovector h (fun y => B y))) x) ^ 2 := by
    subst h
    cases eq_of_heq hD
    rfl
  rw [htransport _ _ _ _ G.initial_metric G.initial_connection]
  exact rotational_linear_skew_gradient_normSq_le g₀.connection g₀.rotation_invariant
    g₀.nonnegative_sectional g₀.complete B hB x

theorem raw_initial_metricLieDerivative_eq {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (B : StandardCapSpace → StandardCapSpace)
    (x u v : StandardCapSpace) :
    DeTurckNative.metricLieDerivative (G.flow.connection 0) B x u v =
      DeTurckNative.metricLieDerivative g₀.connection B x u v := by
  have htransport (g h : RiemannianMetric 3 StandardCapSpace)
      (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h) (hD : HEq D D') :
      DeTurckNative.metricLieDerivative D B x u v =
        DeTurckNative.metricLieDerivative D' B x u v := by
    subst h
    cases eq_of_heq hD
    rfl
  exact htransport _ _ _ _ G.initial_metric G.initial_connection

theorem raw_initial_heat_gradient_bound {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (hB : ∀ x, inner ℝ x (B x) = 0)
    (X : ℝ → StandardCapSpace → StandardCapSpace) (hX : ContDiff ℝ ∞ (X 0))
    {x : StandardCapSpace} (he : X 0 =ᶠ[𝓝 x] fun y => B y) :
    vectorHeatJetEnergy G X 1 0 x ≤ 9 * ‖B‖ ^ 2 := by
  change ((G.flow.metric 0).tensorNorm ((G.flow.connection 0).covariantTensorDerivative
    (killingCovector (G.flow.metric 0) (X 0))) x) ^ 2 ≤ _
  rw [covector_gradient_normSq_eq_of_field_germ (G.flow.connection 0) hX B.contDiff he]
  exact raw_initial_rotation_gradient_bound G B hB x

theorem raw_initial_heat_killing {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (hB : ∀ x u v : StandardCapSpace,
      DeTurckNative.metricLieDerivative g₀.connection (fun y => B y) x u v = 0)
    (X : ℝ → StandardCapSpace → StandardCapSpace) (hX : ContDiff ℝ ∞ (X 0))
    {x : StandardCapSpace} (he : X 0 =ᶠ[𝓝 x] fun y => B y) (u v : StandardCapSpace) :
    DeTurckNative.metricLieDerivative (G.flow.connection 0) (X 0) x u v = 0 := by
  rw [metricLieDerivative_eq_of_field_germ (G.flow.connection 0)
    (hX.differentiable (by simp) x) B.differentiableAt he,
    raw_initial_metricLieDerivative_eq]
  exact hB x u v

end PoincareConjecture.M35.Uniqueness.Heat
