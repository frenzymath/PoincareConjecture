import PoincareConjecture.Proofs.M35.CapGeometry.M27ProductChartMetric
import PoincareConjecture.Proofs.M35.CapGeometry.RoundProductRicci









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "Ip" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}



theorem sphereLineChart_contMDiff (N : M27SphereLineFlowCertificate K)
    (q : UnitTwoSphere) : ContMDiff (𝓡 3) (𝓡 3) ∞
      (N.identification ∘ cylinderChart q) :=
  N.identification.contMDiff.comp (cylinderChart_contMDiff q)


theorem sphereLineChart_invertible (N : M27SphereLineFlowCertificate K)
    (q : UnitTwoSphere) (x : V) :
    (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) x).IsInvertible := by
  have hN := N.identification.isLocalDiffeomorph
  have hNi : (mfderiv Ip (𝓡 3) N.identification (cylinderChart q x)).IsInvertible :=
    ⟨hN.mfderivToContinuousLinearEquiv (by simp) _, rfl⟩
  rw [mfderiv_comp x (N.identification.contMDiff.mdifferentiable (by simp) _)
    ((cylinderChart_contMDiff q).mdifferentiable (by simp) x)]
  exact hNi.comp (cylinderChart_mfderiv_invertible q x)


noncomputable def sphereLineChartMetric (N : M27SphereLineFlowCertificate K)
    (t : ℝ) (q : UnitTwoSphere) : RiemannianMetric 3 V :=
  RiemannianMetric.ofEuclideanCoefficients
    ((K.flow.metric t).pullbackCoefficients (N.identification ∘ cylinderChart q))
    (contDiff_iff_contDiffAt.mpr fun x =>
      (K.flow.metric t).contDiffAt_pullbackCoefficients (sphereLineChart_contMDiff N q x))
    (fun x u v => (K.flow.metric t).symm (N.identification (cylinderChart q x))
      (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) x u)
      (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) x v))
    (fun x v hv => (K.flow.metric t).pos (N.identification (cylinderChart q x))
      (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) x v)
      (fun hz => hv ((sphereLineChart_invertible N q x).injective
        (hz.trans (map_zero (mfderiv (𝓡 3) (𝓡 3)
          (N.identification ∘ cylinderChart q) x)).symm))))


noncomputable def sphereLineChartConnection (N : M27SphereLineFlowCertificate K)
    (t : ℝ) (q : UnitTwoSphere) : LeviCivitaData (sphereLineChartMetric N t q) :=
  (sphereLineChartMetric N t q).euclideanLeviCivitaData


theorem sphereLineChartMetric_product (N : M27SphereLineFlowCertificate K)
    (t : ℝ) (ht : t ≤ 0) (q : UnitTwoSphere) (x u v : V) :
    (sphereLineChartMetric N t q).inner x u v =
      (m27SphereChartMetric N.sphere t q).inner (cylinderCoordinateEquiv x).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2 := by
  change (K.flow.metric t).inner (N.identification (cylinderChart q x))
    (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) x u)
    (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) x v) = _
  rw [mfderiv_comp_apply x (N.identification.contMDiff.mdifferentiable (by simp) _)
    ((cylinderChart_contMDiff q).mdifferentiable (by simp) x),
    mfderiv_comp_apply x (N.identification.contMDiff.mdifferentiable (by simp) _)
    ((cylinderChart_contMDiff q).mdifferentiable (by simp) x), N.metric_transport t ht]
  rw [M27RoundSphereFamily.productInner, mfderiv_cylinderChart, mfderiv_cylinderChart]
  rfl



theorem sphereLineChartMetric_hasDerivWithinAt (N : M27SphereLineFlowCertificate K)
    (t : ℝ) (ht : t ≤ 0) (q : UnitTwoSphere) (x u v : V) :
    HasDerivWithinAt (fun s => (sphereLineChartMetric N s q).inner x u v)
      (-2 * (sphereLineChartConnection N t q).ricci x u v) (Iic 0) t := by
  let f := N.identification ∘ cylinderChart q
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : V,
      (sphereLineChartMetric N t q).inner y a b = (K.flow.metric t).inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y a) (mfderiv (𝓡 3) (𝓡 3) f y b) :=
    Eventually.of_forall fun _ _ _ => rfl
  have hricci := (sphereLineChartConnection N t q).ricci_eq_pullback_euclidean
    (K.flow.connection t) (sphereLineChart_contMDiff N q x)
    (Eventually.of_forall (sphereLineChart_invertible N q)) hmetric u v
  rw [hricci]
  exact K.flow.equation t ht (f x)
    (mfderiv (𝓡 3) (𝓡 3) f x u) (mfderiv (𝓡 3) (𝓡 3) f x v)

end PoincareConjecture.M35
