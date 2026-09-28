import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.SmoothAtlas
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gluing.Descent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter TopologicalSpace PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} {hcomparison : RayComparison p} {n : ℕ}

def UnitSliceRadialChartData.levelMetric (d : UnitSliceRadialChartData hcomparison n) :
    RiemannianMetric n d.Level :=
  d.metric.regularLevelMetric d.smooth d.source d.regular (1 / 2)

theorem exists_unique_unitSliceMetric
    (hcover : ∀ x : AsymptoticConeUnitSlice p hcomparison,
      ∃ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level),
        (d.levelHomeomorph z).1 = x) :
    letI := unitSliceChartedSpace hcomparison n hcover
    letI := unitSlice_isManifold hcomparison n hcover
    ∃! gL : RiemannianMetric n (AsymptoticConeUnitSlice p hcomparison),
      ∀ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level)
        (v w : TangentSpace (𝓡 n) z),
        d.levelMetric.inner z v w = gL.inner (d.levelHomeomorph z).1
          (mfderiv (𝓡 n) (𝓡 n) (fun y : d.Level => (d.levelHomeomorph y).1) z v)
          (mfderiv (𝓡 n) (𝓡 n) (fun y : d.Level => (d.levelHomeomorph y).1) z w) := by
  let := unitSliceChartedSpace hcomparison n hcover
  let := unitSlice_isManifold hcomparison n hcover
  let q := fun (d : UnitSliceRadialChartData hcomparison n) (z : d.Level) =>
    (d.levelHomeomorph z).1
  have hq (d : UnitSliceRadialChartData hcomparison n) :
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q d) :=
    d.isLocalDiffeomorph_levelMap hcomparison n hcover
  apply Poincare.Gluing.exists_unique_metric_of_covering_local_diffeomorphisms
    (fun d : UnitSliceRadialChartData hcomparison n => d.levelMetric) q hq hcover
  intro d e z z' hzz a b a' b' ha hb
  let T := d.levelTransition e z z'
  have hz : z ∈ T.source := by
    refine ⟨by simp, ?_⟩
    change d.levelEmbedding z z ∈ (e.levelEmbedding z').target
    rw [d.levelEmbedding_apply, show (d.levelHomeomorph z).1 = (e.levelHomeomorph z').1 from hzz]
    exact (e.levelEmbedding z').map_source (by simp)
  have hTz : T z = z' := by
    change (e.levelEmbedding z').symm (d.levelEmbedding z z) = z'
    rw [show d.levelEmbedding z z = e.levelEmbedding z' z' from hzz]
    exact (e.levelEmbedding z').left_inv (by simp)
  have hnear : q e ∘ T =ᶠ[𝓝 z] q d := by
    filter_upwards [T.open_source.mem_nhds hz] with y hy
    apply Subtype.ext
    exact d.levelTransition_ambient e z z' hy
  have hdt : MDifferentiableAt (𝓡 n) (𝓡 n) T z :=
    ((d.contMDiffOn_levelTransition e z z').contMDiffAt (T.open_source.mem_nhds hz)).mdifferentiableAt
      (by simp)
  have hderiv : (mfderiv (𝓡 n) (𝓡 n) (q e) (T z)).comp
      (mfderiv (𝓡 n) (𝓡 n) T z) = mfderiv (𝓡 n) (𝓡 n) (q d) z := by
    rw [← mfderiv_comp z ((hq e).mdifferentiable (by simp) _) hdt]
    exact hnear.mfderiv_eq
  let L := (hq e).mfderivToContinuousLinearEquiv (by simp) z'
  have hda : mfderiv (𝓡 n) (𝓡 n) T z a = a' := by
    apply L.injective
    have hh := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) => A a) hderiv
    rw [hTz] at hh
    exact hh.trans ha
  have hdb : mfderiv (𝓡 n) (𝓡 n) T z b = b' := by
    apply L.injective
    have hh := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) => A b) hderiv
    rw [hTz] at hh
    exact hh.trans hb
  have hm := d.regularLevelMetric_levelTransition e z z' hz a b
  change e.levelMetric.inner (T z)
    (mfderiv (𝓡 n) (𝓡 n) T z a) (mfderiv (𝓡 n) (𝓡 n) T z b) =
      d.levelMetric.inner z a b at hm
  rw [hda, hdb, hTz] at hm
  exact hm.symm

def unitSliceMetric
    (hcover : ∀ x : AsymptoticConeUnitSlice p hcomparison,
      ∃ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level),
        (d.levelHomeomorph z).1 = x) :
    letI := unitSliceChartedSpace hcomparison n hcover
    letI := unitSlice_isManifold hcomparison n hcover
    RiemannianMetric n (AsymptoticConeUnitSlice p hcomparison) :=
  (exists_unique_unitSliceMetric hcover).exists.choose

theorem unitSliceMetric_inner
    (hcover : ∀ x : AsymptoticConeUnitSlice p hcomparison,
      ∃ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level),
        (d.levelHomeomorph z).1 = x) :
    letI := unitSliceChartedSpace hcomparison n hcover
    letI := unitSlice_isManifold hcomparison n hcover
    ∀ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level)
      (v w : TangentSpace (𝓡 n) z),
      d.levelMetric.inner z v w = (unitSliceMetric hcover).inner (d.levelHomeomorph z).1
        (mfderiv (𝓡 n) (𝓡 n) (fun y : d.Level => (d.levelHomeomorph y).1) z v)
        (mfderiv (𝓡 n) (𝓡 n) (fun y : d.Level => (d.levelHomeomorph y).1) z w) :=
  (exists_unique_unitSliceMetric hcover).exists.choose_spec

end Poincare.AncientVolume.ScalarRatio

universe u

namespace PoincareConjecture.RicciFlow

open Poincare.AncientVolume.ScalarRatio

theorem exists_unitSliceMetric_of_zero_ratio
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
    ∃ gL : RiemannianMetric n (AsymptoticConeUnitSlice p hc),
      ∀ (d : UnitSliceRadialChartData hc n) (z : d.Level)
        (v w : TangentSpace (𝓡 n) z),
        d.levelMetric.inner z v w = gL.inner (d.levelHomeomorph z).1
          (mfderiv (𝓡 n) (𝓡 n) (fun y : d.Level => (d.levelHomeomorph y).1) z v)
          (mfderiv (𝓡 n) (𝓡 n) (fun y : d.Level => (d.levelHomeomorph y).1) z w) := by
  let := (F.metric t₀).toMetricSpace
  exact (exists_unique_unitSliceMetric
    (F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
      hK hbound hκ hnoncollapse t₀ ht₀ p hzero)).exists

end PoincareConjecture.RicciFlow
