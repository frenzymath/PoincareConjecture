import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.AngularPaths
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Antipodal
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Connected.PathConnected









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture
open scoped Topology Manifold ContDiff

namespace Poincare.AncientVolume.ScalarRatio

private theorem exists_nearby_ne_of_chartedSpace
    {n : ℕ} (hn : 1 ≤ n) {S : Type*} [MetricSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S] (x : S) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : S, y ≠ x ∧ dist x y < ε := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let : PerfectSpace (EuclideanSpace ℝ (Fin n)) := perfectSpace_of_module ℝ _
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hx : x ∈ e.source := mem_chart_source _ x
  have hxe : e x ∈ e.target := e.map_source hx
  have he : ContinuousAt e.symm (e x) := e.continuousAt_symm hxe
  have hball : e.symm ⁻¹' Metric.ball x ε ∈ 𝓝 (e x) := by
    apply he.preimage_mem_nhds
    simpa only [e.left_inv hx] using Metric.ball_mem_nhds x hε
  obtain ⟨u, hu, hune⟩ := nhdsWithin_neBot.mp
    (inferInstance : NeBot (𝓝[≠] (e x)))
    (inter_mem (e.open_target.mem_nhds hxe) hball)
  have hneq : u ≠ e x := by simpa using hune
  refine ⟨e.symm u, ?_, ?_⟩
  · intro h
    exact hneq ((e.right_inv hu.1).symm.trans (congrArg e h))
  · simpa only [mem_preimage, Metric.mem_ball, dist_comm] using hu.2

theorem asymptoticConeUnitSlice_dist_le_two
    {X : Type*} [MetricSpace X] {p : X} (hc : RayComparison p)
    (x y : AsymptoticConeUnitSlice p hc) : dist x y ≤ 2 := by
  let u := (asymptoticConeUnitIsometry hc).symm x
  let o := asymptoticConeProjection hc (0, u)
  have ho (z : AsymptoticConeUnitSlice p hc) : dist z.1 o = 1 := by
    obtain ⟨v, rfl⟩ := surjective_asymptoticConeUnitProjection hc z
    exact dist_asymptoticConeProjection_zero hc 1 v u
  calc
    dist x y = dist x.1 y.1 := rfl
    _ ≤ dist x.1 o + dist o y.1 := dist_triangle _ _ _
    _ = 2 := by rw [ho x, dist_comm o, ho y]; norm_num

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio



theorem pathConnectedSpace_asymptoticConeUnitSlice_of_chartedSpace
    {n k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M)
    (hk : 1 ≤ k) :
    letI := g.toMetricSpace
    let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
    ∀ (_ : ChartedSpace (EuclideanSpace ℝ (Fin k)) (AsymptoticConeUnitSlice p hc)),
      PathConnectedSpace (AsymptoticConeUnitSlice p hc) := by
  let := g.toMetricSpace
  let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
  dsimp only
  intro charts
  let := charts
  refine ⟨nonempty_asymptoticConeUnitSlice hc (g.nonempty_basedMinimizingRays hcomplete p), ?_⟩
  have hjoin (x y : AsymptoticConeUnitSlice p hc) (hxy : dist x y < 2) : Joined x y := by
    obtain ⟨γ, hγ0, hγ1, hγ, _, _, P, _⟩ :=
      g.exists_asymptoticCone_angular_path D hcomplete hsec p x y hxy
    exact ⟨P⟩
  intro x y
  by_cases hxy : dist x y < 2
  · exact hjoin x y hxy
  have heq : dist x y = 2 := le_antisymm
    (asymptoticConeUnitSlice_dist_le_two hc x y) (le_of_not_gt hxy)
  obtain ⟨z, hzx, hxz⟩ := exists_nearby_ne_of_chartedSpace hk x (by norm_num : (0 : ℝ) < 2)
  have hbound := g.asymptoticConeUnitSlice_dist_sq_add_le_four_of_antipodal
    D hcomplete hsec p x y z heq
  have hpos : 0 < dist x z := dist_pos.mpr hzx.symm
  have hyz : dist y z < 2 := by nlinarith [dist_nonneg (x := y) (y := z)]
  exact (hjoin x z hxz).trans (hjoin y z hyz).symm

end PoincareConjecture.RiemannianMetric

universe u

namespace PoincareConjecture.RicciFlow

open Poincare.AncientVolume.ScalarRatio



theorem unitSlice_pathConnected_of_zero_ratio
    {n : ℕ} (hn : 1 ≤ n) {M : Type u} [TopologicalSpace M] [T3Space M]
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
    PathConnectedSpace (AsymptoticConeUnitSlice p hc) := by
  let := (F.metric t₀).toMetricSpace
  let hsec : (F.connection t₀).NonnegativeSectionalCurvature := fun x v w =>
    (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  let hc := (F.metric t₀).rayComparison_of_metricComplete
    (F.connection t₀) (hcomplete t₀ ht₀) hsec p
  let hcover := F.unitSliceRadialAtlas_covers_of_zero_ratio hC hcomplete hoperator
    hK hbound hκ hnoncollapse t₀ ht₀ p hzero
  exact (F.metric t₀).pathConnectedSpace_asymptoticConeUnitSlice_of_chartedSpace
    (F.connection t₀) (hcomplete t₀ ht₀) hsec p hn (unitSliceChartedSpace hc n hcover)

end PoincareConjecture.RicciFlow
