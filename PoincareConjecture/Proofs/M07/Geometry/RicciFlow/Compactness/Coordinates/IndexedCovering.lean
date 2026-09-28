import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.Covering
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.JetBounds












noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture


structure NormalChartCover {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : ℝ → RiemannianMetric n M) (p : M) (T' T A R ρ a b : ℝ) (N : ℕ) where
  centre : Fin (N + 1) → M
  chart : Fin (N + 1) → PartialDiffeomorph (𝓡 n) (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) M ∞
  centre_zero : centre 0 = p
  centre_mem : ∀ i, centre i ∈ (g 0).ball p A
  source : ∀ i, (chart i).source = Metric.ball 0 R
  target : ∀ i, (chart i).target = (g 0).ball (centre i) R
  map_zero : ∀ i, chart i 0 = centre i
  normalized : ∀ i, ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
    (∀ u v, (g 0).pullbackCoefficients (extChartAt (𝓡 n) (centre i)).symm
      (extChartAt (𝓡 n) (centre i) (centre i)) (L u) (L v) = inner ℝ u v) ∧
    HasFDerivAt (fun w => extChartAt (𝓡 n) (centre i) (chart i w))
      L.toContinuousLinearMap 0
  radial_geodesic : ∀ i, ∀ w ∈ Metric.ball 0 R,
    (g 0).IsGeodesicOn (fun t => chart i (t • w))
      {t : ℝ | t • w ∈ Metric.ball 0 R}
  radial_distance : ∀ i, ∀ w ∈ Metric.ball 0 R,
    (g 0).edist (centre i) (chart i w) = ENNReal.ofReal ‖w‖
  coefficients : ∀ i, ∀ t ∈ Ioo T' T, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ v,
    a * ‖v‖ ^ 2 ≤ (g t).pullbackCoefficients (chart i) x v v ∧
    (g t).pullbackCoefficients (chart i) x v v ≤ b * ‖v‖ ^ 2
  distances : ∀ i, ∀ x ∈ Metric.ball 0 (ρ / 2), ∀ y ∈ Metric.ball 0 (ρ / 2),
    Real.sqrt a * dist x y ≤ ((g 0).edist (chart i x) (chart i y)).toReal ∧
    ((g 0).edist (chart i x) (chart i y)).toReal ≤ Real.sqrt b * dist x y
  compact_image : ∀ i, IsCompact ((chart i) '' Metric.closedBall 0 (ρ / 4))
  cover : (g 0).ball p A ⊆ ⋃ i, (chart i) '' Metric.closedBall 0 (ρ / 4)

namespace NormalChartCover


def HasMetricJetBound {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {p : M} {T' T A R ρ a b : ℝ} {N : ℕ}
    (C : NormalChartCover g p T' T A R ρ a b N) (m : ℕ) (B : ℝ) : Prop :=
  ∀ i x, x ∈ Metric.closedBall 0 ρ →
    ‖iteratedFDeriv ℝ m ((g 0).pullbackCoefficients (C.chart i)) x‖ ≤ B

end NormalChartCover

private theorem exists_surjective_fin_with_zero {α : Type*} [Fintype α]
    (a : α) {N : ℕ} (hN : Fintype.card α ≤ N) :
    ∃ f : Fin (N + 1) → α, f 0 = a ∧ Function.Surjective f := by
  classical
  let : Nonempty α := ⟨a⟩
  let e : α ↪ Fin N :=
    { toFun := fun x => ⟨(Fintype.equivFin α x).val,
        (Fintype.equivFin α x).isLt.trans_le hN⟩
      inj' := fun x y h => (Fintype.equivFin α).injective
        (Fin.ext (congrArg (fun z : Fin N => z.val) h)) }
  refine ⟨Fin.cases a (Function.invFun e), rfl, ?_⟩
  intro x
  exact ⟨(e x).succ, Function.leftInverse_invFun e.injective x⟩

namespace PointedRicciFlowCompactnessHypotheses


theorem eventually_nonempty_normalChartCover
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hn : 1 ≤ n) {A : ℝ} (hA : 0 < A) :
    ∃ R ρ a b : ℝ, 0 < ρ ∧ 2 * ρ < R ∧ 0 < a ∧ 0 < b ∧
      ∃ N : ℕ, ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      Nonempty (NormalChartCover F.metricAt F.base T' T A R ρ a b N) := by
  classical
  obtain ⟨R, ρ, a, b, hρ, hρR, ha, hb, N, hcover⟩ :=
    H.eventually_exists_uniform_exponential_cover hn hA
  refine ⟨R, ρ, a, b, hρ, hρR, ha, hb, N, ?_⟩
  filter_upwards [hcover] with k hk
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  obtain ⟨S, hbase, hS, hN, Φ, hΦ, hdist, hcompact, hcover⟩ := hk
  obtain ⟨f, hf0, hf⟩ := exists_surjective_fin_with_zero (⟨F.base, hbase⟩ : S)
    (by simpa only [Fintype.card_coe] using hN)
  choose hsource htarget hzero L hL hderiv hgeo hradial hcoeff using hΦ
  have hcoverFixed : (F.metricAt 0).ball F.base A ⊆
      ⋃ i, (Φ (f i)) '' Metric.closedBall 0 (ρ / 4) := by
    intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨i, rfl⟩ := hf q
    exact mem_iUnion.mpr ⟨i, hq⟩
  dsimp only
  refine ⟨{
    centre := fun i => f i
    chart := fun i => Φ (f i)
    centre_zero := congrArg Subtype.val hf0
    centre_mem := fun i => hS (f i).property
    source := fun i => hsource (f i)
    target := fun i => htarget (f i)
    map_zero := fun i => hzero (f i)
    normalized := fun i => ⟨L (f i), hL (f i), hderiv (f i)⟩
    radial_geodesic := fun i => hgeo (f i)
    radial_distance := fun i => hradial (f i)
    coefficients := fun i => hcoeff (f i)
    distances := fun i => hdist (f i)
    compact_image := fun i => hcompact (f i)
    cover := hcoverFixed }⟩


theorem eventually_normalChartCover_metric_jet_bound_of_local_derivative_estimates
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ) (hρR : ρ < R) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ C : NormalChartCover F.metricAt F.base T' T A R ρ a b N,
        C.HasMetricJetBound m B := by
  obtain ⟨B, hB, hbound⟩ :=
    H.eventually_uniform_zero_time_exponential_metric_jet_bound_of_local_derivative_estimates
      hShi hA hρ hρR m
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound] with k hk
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  dsimp only
  intro C i x hx
  obtain ⟨L, hL, hderiv⟩ := C.normalized i
  exact hk (C.centre i) (C.centre_mem i) L (C.chart i) (C.source i) (C.target i)
    (C.map_zero i) hL hderiv (C.radial_geodesic i) x hx


theorem eventually_normalChartCover_metric_jet_bound
    {n : ℕ} {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hM04 : RicciFlowCurvatureTheory.{0})
    {A R ρ a b : ℝ} {N : ℕ} (hA : 0 < A) (hρ : 0 < ρ) (hρR : ρ < R) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ C : NormalChartCover F.metricAt F.base T' T A R ρ a b N,
        C.HasMetricJetBound m B :=
  H.eventually_normalChartCover_metric_jet_bound_of_local_derivative_estimates
    hM04.local_derivative_estimates hA hρ hρR m

end PointedRicciFlowCompactnessHypotheses
end PoincareConjecture
