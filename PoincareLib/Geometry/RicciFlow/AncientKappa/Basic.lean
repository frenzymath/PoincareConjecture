import PoincareLib.Geometry.RicciFlow.Compactness.Pointed
import PoincareLib.Geometry.Riemannian.Measure.Calibrated
import PoincareLib.Geometry.RicciFlow.Harnack.Basic

/-!
# Ancient kappa-solutions and rescalings

Declaration bodies from `PoincareMT/Definitions/Ch09/AsymptoticSoliton.lean`
at Mapher commit `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Morgan--Tian, Definitions 9.1--9.2, pp. 179--180.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- The all-scales noncollapsing condition on an ancient fixed-carrier flow. -/
def AncientKappaNoncollapsed (F : RicciFlow n M (Set.Iic 0)) (κ : ℝ) : Prop :=
  ∀ r₀ : ℝ, 0 < r₀ →
    ∀ (t : ℝ), t ≤ 0 → ∀ p : M, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∀ s ∈ Set.Ioc (t - r ^ 2) t, ∀ q ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball p r)

/-- An ancient complete nonflat flow with bounded nonnegative curvature. -/
structure AncientKappaSolution (n : ℕ) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M] where
  flow : RicciFlow n M (Set.Iic 0)
  kappa : ℝ
  kappa_pos : 0 < kappa
  complete : ∀ t : ℝ, t ≤ 0 → MetricComplete (flow.metric t)
  nonnegative_curvature_operator :
    ∀ t : ℝ, t ≤ 0 → ∀ x : M,
      LeviCivitaData.NonnegativeCurvatureOperator (flow.connection t) x
  bounded_curvature : ∀ t : ℝ, t ≤ 0 → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : M, |(flow.connection t).curvatureTensorNorm x| ≤ K
  nonflat : ∀ t : ℝ, t ≤ 0 → ∃ x : M,
    (flow.connection t).curvatureTensorNorm x ≠ 0
  noncollapsed : AncientKappaNoncollapsed flow kappa

/-- A rescaled ancient flow `g_k(t) = tau⁻¹ g(tau * t)`. -/
structure AncientRescaling (K : AncientKappaSolution n M) (tau : ℝ) where
  tau_pos : 0 < tau
  flow : RicciFlow n M (Set.Iio 0)
  metric_scale : ∀ t : ℝ, t < 0 → ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
    (flow.metric t).inner x v w =
      (1 / tau) * (K.flow.metric (tau * t)).inner x v w
  ricci_scale : ∀ t : ℝ, t < 0 → ∀ x : M,
    ∀ v w : TangentSpace (𝓡 n) x,
      (flow.connection t).ricci x v w =
        (K.flow.connection (tau * t)).ricci x v w
  scalar_scale : ∀ t : ℝ, t < 0 → ∀ x : M,
    (flow.connection t).scalarCurvature x =
      tau * (K.flow.connection (tau * t)).scalarCurvature x
  curvature_norm_scale : ∀ t : ℝ, t < 0 → ∀ x : M,
    (flow.connection t).curvatureTensorNorm x =
      tau * (K.flow.connection (tau * t)).curvatureTensorNorm x

end PoincareMT
