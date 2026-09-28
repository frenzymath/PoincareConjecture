import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialLevelCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} {hcomparison : RayComparison p} {n : ℕ}



theorem UnitSliceRadialChartData.levelMetric_curvatureTensor_eq_one
    (d : UnitSliceRadialChartData hcomparison n) (z : d.Level)
    (u v w a : TangentSpace (𝓡 n) z) :
    d.levelMetric.leviCivitaData.curvatureTensor z u v w a =
      d.levelMetric.inner z u w * d.levelMetric.inner z v a -
        d.levelMetric.inner z u a * d.levelMetric.inner z v w := by
  let : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  apply d.connection.radialLevel_curvatureTensor_eq_one d.smooth d.source d.regular
    d.hessian d.eikonal
  intro x hx b c e f
  apply abs_nonpos_iff.mp
  simpa only [d.flat x hx, zero_mul] using
    d.connection.abs_curvatureTensor_le_tangentNorm x b c e f

variable (hcover : ∀ x : AsymptoticConeUnitSlice p hcomparison,
  ∃ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level),
    (d.levelHomeomorph z).1 = x)



theorem curvatureTensor_eq_one_of_unitSliceMetric_pullback :
    letI := unitSliceChartedSpace hcomparison n hcover
    letI := unitSlice_isManifold hcomparison n hcover
    ∀ (gL : RiemannianMetric n (AsymptoticConeUnitSlice p hcomparison)),
      (∀ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level)
        (v w : TangentSpace (𝓡 n) z),
        d.levelMetric.inner z v w = gL.inner (d.levelHomeomorph z).1
          (mfderiv (𝓡 n) (𝓡 n) (fun y : d.Level => (d.levelHomeomorph y).1) z v)
          (mfderiv (𝓡 n) (𝓡 n) (fun y : d.Level => (d.levelHomeomorph y).1) z w)) →
      ∀ (x : AsymptoticConeUnitSlice p hcomparison) (u v w a : TangentSpace (𝓡 n) x),
        gL.leviCivitaData.curvatureTensor x u v w a =
          gL.inner x u w * gL.inner x v a - gL.inner x u a * gL.inner x v w := by
  let := unitSliceChartedSpace hcomparison n hcover
  let := unitSlice_isManifold hcomparison n hcover
  intro gL hmetric x u v w a
  obtain ⟨d, z, rfl⟩ := hcover x
  let q : d.Level → AsymptoticConeUnitSlice p hcomparison := fun y => (d.levelHomeomorph y).1
  have hq := d.isLocalDiffeomorph_levelMap hcomparison n hcover
  let L := hq.mfderivToContinuousLinearEquiv (by simp) z
  have hR := d.levelMetric.leviCivitaData.curvatureTensor_eq_of_local_isometry
    gL.leviCivitaData isOpen_univ hq.contMDiff.contMDiffOn
    (fun y _ b c => hmetric d y b c) (Set.mem_univ z)
    (L.symm u) (L.symm v) (L.symm w) (L.symm a)
  have hL (b : TangentSpace (𝓡 n) (q z)) :
      mfderiv (𝓡 n) (𝓡 n) (fun y : d.Level => (d.levelHomeomorph y).1) z (L.symm b) = b :=
    L.apply_symm_apply b
  have hm (b c : TangentSpace (𝓡 n) (q z)) :
      d.levelMetric.inner z (L.symm b) (L.symm c) = gL.inner (q z) b c := by
    rw [hmetric]
    exact congrArg₂ (fun v w => gL.inner (q z) v w) (hL b) (hL c)
  rw [d.levelMetric_curvatureTensor_eq_one, hm, hm, hm, hm] at hR
  simpa only [hL] using hR.symm



theorem unitSliceMetric_curvatureTensor_eq_one :
    letI := unitSliceChartedSpace hcomparison n hcover
    letI := unitSlice_isManifold hcomparison n hcover
    ∀ (x : AsymptoticConeUnitSlice p hcomparison) (u v w a : TangentSpace (𝓡 n) x),
      (unitSliceMetric hcover).leviCivitaData.curvatureTensor x u v w a =
        (unitSliceMetric hcover).inner x u w * (unitSliceMetric hcover).inner x v a -
          (unitSliceMetric hcover).inner x u a * (unitSliceMetric hcover).inner x v w := by
  let := unitSliceChartedSpace hcomparison n hcover
  let := unitSlice_isManifold hcomparison n hcover
  exact curvatureTensor_eq_one_of_unitSliceMetric_pullback hcover
    (unitSliceMetric hcover) (unitSliceMetric_inner hcover)



theorem unitSliceMetric_sectionalCurvature_eq_one :
    letI := unitSliceChartedSpace hcomparison n hcover
    letI := unitSlice_isManifold hcomparison n hcover
    ∀ (x : AsymptoticConeUnitSlice p hcomparison) (u v : TangentSpace (𝓡 n) x),
      (unitSliceMetric hcover).inner x u u * (unitSliceMetric hcover).inner x v v -
        (unitSliceMetric hcover).inner x u v ^ 2 ≠ 0 →
      (unitSliceMetric hcover).leviCivitaData.sectionalCurvature x u v = 1 := by
  let := unitSliceChartedSpace hcomparison n hcover
  let := unitSlice_isManifold hcomparison n hcover
  intro x u v hplane
  unfold LeviCivitaData.sectionalCurvature
  rw [unitSliceMetric_curvatureTensor_eq_one hcover x u v u v,
    (unitSliceMetric hcover).symm x v u, ← pow_two]
  exact div_self hplane

end Poincare.AncientVolume.ScalarRatio

universe u

namespace PoincareConjecture.RicciFlow

open Poincare.AncientVolume.ScalarRatio




theorem unitSliceMetric_curvature_one_of_zero_ratio
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (n + 1) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ (n + 1)) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M)
    (hzero : ∀ C : ℝ, 0 < C → ∃ L : ℝ, ∀ x : M,
      L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C) :
    letI := (F.metric t₀).toMetricSpace
    let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
      (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t₀ ht₀ x) v w
    let hc := (F.metric t₀).rayComparison_of_metricComplete
      (F.connection t₀) (hcomplete t₀ ht₀) hsec p
    let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse t₀ ht₀ p hzero
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    let gL := unitSliceMetric hcover
    (∀ (x : AsymptoticConeUnitSlice p hc) (u v w a : TangentSpace (𝓡 n) x),
      gL.leviCivitaData.curvatureTensor x u v w a =
        gL.inner x u w * gL.inner x v a - gL.inner x u a * gL.inner x v w) ∧
    (∀ (x : AsymptoticConeUnitSlice p hc) (u v : TangentSpace (𝓡 n) x),
      gL.inner x u u * gL.inner x v v - gL.inner x u v ^ 2 ≠ 0 →
      gL.leviCivitaData.sectionalCurvature x u v = 1) := by
  let := (F.metric t₀).toMetricSpace
  let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
    hK hbound hκ hnoncollapse t₀ ht₀ p hzero
  exact ⟨unitSliceMetric_curvatureTensor_eq_one hcover, unitSliceMetric_sectionalCurvature_eq_one hcover⟩

end PoincareConjecture.RicciFlow
