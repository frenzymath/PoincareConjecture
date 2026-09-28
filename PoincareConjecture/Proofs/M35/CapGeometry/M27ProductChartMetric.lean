import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCharts
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "Ip" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private noncomputable def chartMetric
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (f : EuclideanSpace ℝ (Fin n) → M)
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hi : ∀ x, (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible) :
    RiemannianMetric n (EuclideanSpace ℝ (Fin n)) :=
  RiemannianMetric.ofEuclideanCoefficients (g.pullbackCoefficients f)
    (contDiff_iff_contDiffAt.mpr fun x => g.contDiffAt_pullbackCoefficients (hf x))
    (fun x u v => g.symm (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
      (mfderiv (𝓡 n) (𝓡 n) f x v))
    (fun x v hv => g.pos (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
      (fun hz => hv ((hi x).injective
      (hz.trans (map_zero (mfderiv (𝓡 n) (𝓡 n) f x)).symm))))

theorem m27_sphereChart_contMDiff (q : UnitTwoSphere) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (chartAt E2 q).symm := by
  intro x
  have hx : x ∈ (chartAt E2 q).target := by rw [sphere_chart_target]; trivial
  exact (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) x hx).contMDiffAt
    ((chartAt E2 q).open_target.mem_nhds hx)

theorem m27_sphereChart_invertible (q : UnitTwoSphere) (x : E2) :
    (mfderiv (𝓡 2) (𝓡 2) (chartAt E2 q).symm x).IsInvertible := by
  have hx : x ∈ (extChartAt (𝓡 2) q).target := by simp [sphere_chart_target]
  have h := isInvertible_mfderivWithin_extChartAt_symm hx
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
  exact h

noncomputable def m27SphereChartMetric (F : M27RoundSphereFamily) (t : ℝ)
    (q : UnitTwoSphere) : RiemannianMetric 2 E2 :=
  chartMetric (F.metric t) (chartAt E2 q).symm
    (m27_sphereChart_contMDiff q) (m27_sphereChart_invertible q)

noncomputable def m27SphereChartConnection (F : M27RoundSphereFamily) (t : ℝ)
    (q : UnitTwoSphere) : LeviCivitaData (m27SphereChartMetric F t q) :=
  (m27SphereChartMetric F t q).euclideanLeviCivitaData

theorem m27SphereChartMetric_round (F : M27RoundSphereFamily) (t : ℝ) (ht : t ≤ 0)
    (q : UnitTwoSphere) : ConstantPositiveSectionalCurvature (m27SphereChartMetric F t q)
      (m27SphereChartConnection F t q) := by
  obtain ⟨c, hc, hround⟩ := F.round t ht
  refine ⟨c, hc, ?_⟩
  intro x u v hu hv huv
  let f := (chartAt E2 q).symm
  let A := mfderiv (𝓡 2) (𝓡 2) f x
  have hm : ∀ᶠ y in 𝓝 x, ∀ a b : E2,
      (m27SphereChartMetric F t q).inner y a b =
        (F.metric t).inner (f y) (mfderiv (𝓡 2) (𝓡 2) f y a)
          (mfderiv (𝓡 2) (𝓡 2) f y b) := Eventually.of_forall fun _ _ _ => rfl
  have hu' : (F.metric t).inner (f x) (A u) (A u) = 1 := hu
  have hv' : (F.metric t).inner (f x) (A v) (A v) = 1 := hv
  have huv' : (F.metric t).inner (f x) (A u) (A v) = 0 := huv
  have hr := hround (f x) (A u) (A v) hu' hv' huv'
  have hR := (m27SphereChartConnection F t q).curvatureTensor_eq_pullback_euclidean
    (F.connection t) (m27_sphereChart_contMDiff q x)
    (Eventually.of_forall (m27_sphereChart_invertible q)) hm u v u v
  unfold LeviCivitaData.sectionalCurvature at hr ⊢
  rw [hu', hv', huv'] at hr
  rw [hu, hv, huv, hR]
  simpa only [one_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one] using hr

variable {M : Type*} [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem twistedProductChart_contMDiff (N : M27TwistedSphereLineFlowCertificate K)
    (q : UnitTwoSphere) : ContMDiff (𝓡 3) (𝓡 3) ∞ (N.cover ∘ cylinderChart q) :=
  N.cover_local_diffeomorph.contMDiff.comp (cylinderChart_contMDiff q)

theorem twistedProductChart_invertible (N : M27TwistedSphereLineFlowCertificate K)
    (q : UnitTwoSphere) (x : V) :
    (mfderiv (𝓡 3) (𝓡 3) (N.cover ∘ cylinderChart q) x).IsInvertible := by
  have hc : (mfderiv Ip (𝓡 3) N.cover (cylinderChart q x)).IsInvertible :=
    ⟨N.cover_local_diffeomorph.mfderivToContinuousLinearEquiv (by simp) _, rfl⟩
  rw [mfderiv_comp x (N.cover_local_diffeomorph.mdifferentiable (by simp) _)
    ((cylinderChart_contMDiff q).mdifferentiable (by simp) x)]
  exact hc.comp (cylinderChart_mfderiv_invertible q x)

noncomputable def twistedProductChartMetric (N : M27TwistedSphereLineFlowCertificate K)
    (t : ℝ) (q : UnitTwoSphere) : RiemannianMetric 3 V :=
  chartMetric (K.flow.metric t) (N.cover ∘ cylinderChart q)
    (twistedProductChart_contMDiff N q) (twistedProductChart_invertible N q)

noncomputable def twistedProductChartConnection (N : M27TwistedSphereLineFlowCertificate K)
    (t : ℝ) (q : UnitTwoSphere) : LeviCivitaData (twistedProductChartMetric N t q) :=
  (twistedProductChartMetric N t q).euclideanLeviCivitaData

theorem twistedProductChartMetric_product
    (N : M27TwistedSphereLineFlowCertificate K) (t : ℝ) (ht : t ≤ 0)
    (q : UnitTwoSphere) (x u v : V) :
    (twistedProductChartMetric N t q).inner x u v =
      (m27SphereChartMetric N.sphere t q).inner (cylinderCoordinateEquiv x).1
        (cylinderCoordinateEquiv u).1 (cylinderCoordinateEquiv v).1 +
        (cylinderCoordinateEquiv u).2 * (cylinderCoordinateEquiv v).2 := by
  change (K.flow.metric t).inner (N.cover (cylinderChart q x))
    (mfderiv (𝓡 3) (𝓡 3) (N.cover ∘ cylinderChart q) x u)
    (mfderiv (𝓡 3) (𝓡 3) (N.cover ∘ cylinderChart q) x v) = _
  rw [mfderiv_comp_apply x (N.cover_local_diffeomorph.mdifferentiable (by simp) _)
    ((cylinderChart_contMDiff q).mdifferentiable (by simp) x),
    mfderiv_comp_apply x (N.cover_local_diffeomorph.mdifferentiable (by simp) _)
    ((cylinderChart_contMDiff q).mdifferentiable (by simp) x), N.metric_transport t ht]
  rw [M27RoundSphereFamily.productInner, mfderiv_cylinderChart, mfderiv_cylinderChart]
  rfl

end PoincareConjecture.M35
