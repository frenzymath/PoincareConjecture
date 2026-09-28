import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedFiberBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.FiberLimits








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory Function
open Poincare.GromovHausdorff
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle
namespace PoincareConjecture


structure PointedCornerModel (m k : ℕ) (δ H : ℝ) where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [measurable : MeasurableSpace carrier]
  [borel : BorelSpace carrier]
  [separation : T3Space carrier]
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) carrier]
  [smooth : IsManifold (𝓡 (m+k)) ∞ carrier]
  [connected : PreconnectedSpace carrier]
  metric : RiemannianMetric (m+k) carrier
  connection : LeviCivitaData metric
  complete : MetricComplete metric
  sectional_lower : ∀ x (v w : TangentSpace (𝓡 (m+k)) x),
    -1 ≤ connection.sectionalCurvature x v w
  f : Fin k → carrier → ℝ
  h : Fin k → carrier → ℝ
  f_smooth : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (f i)
  h_smooth : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (h i)
  domain : TopologicalSpace.Opens carrier
  unit : ∀ x ∈ domain, ∀ i,
    metric.tangentNorm x (connection.gradient (f i) x) ≤ 1 ∧
    metric.tangentNorm x (connection.gradient (h i) x) ≤ 1
  opposite : ∀ x ∈ domain, ∀ i,
    metric.inner x (connection.gradient (f i) x) (connection.gradient (h i) x) ≤ -1+2*δ
  cross : ∀ x ∈ domain, ∀ i j, i ≠ j →
    |metric.inner x (connection.gradient (f i) x) (connection.gradient (f j) x)| ≤ δ ∧
    |metric.inner x (connection.gradient (f i) x) (connection.gradient (h j) x)| ≤ δ ∧
    |metric.inner x (connection.gradient (h i) x) (connection.gradient (f j) x)| ≤ δ ∧
    |metric.inner x (connection.gradient (h i) x) (connection.gradient (h j) x)| ≤ δ
  tight : ∀ x ∈ domain, ∀ i j, i ≠ j →
    metric.inner x (connection.gradient (f i) x) (connection.gradient (f j) x) ≤ 0
  hessian_upper : ∀ x ∈ domain, ∀ i z,
    connection.hessian (f i) x z z ≤ H * metric.inner x z z ∧
    connection.hessian (h i) x z z ≤ H * metric.inner x z z
  regular : ∀ x ∈ domain, Surjective
    (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) (fun y i => f i y) x)
  value : Fin k → ℝ
  point : openFiber (fun y i => f i y) domain value
  buffer : ∀ y, metric.edist (openFiberIncl (fun y i => f i y) domain value point) y ≤
    ENNReal.ofReal 2 → y ∈ domain
  error : openFiber (fun y i => f i y) domain value → ℝ
  error_continuous : Continuous error
  error_nonneg : ∀ x, 0 ≤ error x
  error_sectional_lower :
    let hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ (fun y i => f i y) :=
      contMDiff_pi_space.mpr f_smooth
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf domain regular value
    letI := isManifold_openFiber (m := m) hf domain regular value
    let gL := metric.openRegularFiberMetric hf domain regular value
    ∀ x (v w : TangentSpace (𝓡 m) x),
      -error x ≤ gL.leviCivitaData.sectionalCurvature x v w

attribute [instance] PointedCornerModel.topology PointedCornerModel.measurable
  PointedCornerModel.borel PointedCornerModel.separation PointedCornerModel.charts
  PointedCornerModel.smooth PointedCornerModel.connected

namespace PointedCornerModel
variable {m k : ℕ} {δ H : ℝ}
abbrev joint (A : PointedCornerModel m k δ H) : A.carrier → Fin k → ℝ :=
  fun x i => A.f i x
theorem joint_smooth (A : PointedCornerModel m k δ H) :
    ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ A.joint :=
  contMDiff_pi_space.mpr A.f_smooth
def ambientPoint (A : PointedCornerModel m k δ H) : A.carrier :=
  openFiberIncl A.joint A.domain A.value A.point
def basedSpace (A : PointedCornerModel m k δ H) : BasedMetricSpaceBundle.{0} :=
  A.metric.toBasedMetricSpace A.ambientPoint
def boundedFiberSection (A : PointedCornerModel m k δ H) : Set A.carrier :=
  openFiberIncl A.joint A.domain A.value ''
    {z : openFiber A.joint A.domain A.value |
      (A.metric.edist A.ambientPoint (openFiberIncl A.joint A.domain A.value z)).toReal ≤ (3/2 : ℝ)}

def weightedRatio (A : PointedCornerModel m k δ H) : ℝ :=
  A.metric.openFiberWeightedAmbientBallRatio A.joint_smooth A.domain A.regular A.value
    A.error A.ambientPoint 1 2
theorem boundedFiberSection_dist_le (A : PointedCornerModel m k δ H)
    (x : A.basedSpace.carrier) (hx : x ∈ A.boundedFiberSection) :
    dist A.basedSpace.base x ≤ (3/2 : ℝ) := by
  obtain ⟨z, hz, rfl⟩ := hx
  exact hz
end PointedCornerModel


def IsExpandingCornerLimit {m k : ℕ} {δ H : ℝ}
    (A : ℕ → PointedCornerModel m k δ H)
    (S : CompatiblePointedCompactSystem.{0})
    (K : TopologicalSpace.NonemptyCompacts S.completedLimit.carrier) : Prop :=
  ProperSpace S.completedLimit.carrier ∧
  (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
    γ 0 = x ∧ γ 1 = y ∧
    ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      dist (γ a) (γ b) = |a-b| * dist x y) ∧
  PointedGHConvergesUnbounded (fun j => (A j).basedSpace) S.completedLimit ∧
  ∃ s t ε : ℕ → ℝ,
    Tendsto s atTop atTop ∧ Tendsto t atTop atTop ∧
    (∀ j, 0 < ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∃ hs : ∀ j, (3/2 : ℝ) < s j, ∃ ht : ∀ j, (3/2 : ℝ) < t j,
    ∃ Q : ∀ j, PointedGHRealization
      (ballModel (A j).basedSpace (s j) ((by norm_num : (0:ℝ)<3/2).trans (hs j)))
      (ballModel S.completedLimit (t j) ((by norm_num : (0:ℝ)<3/2).trans (ht j))),
    Tendsto (fun j => pointedHausdorffDist (Q j)) atTop (𝓝 0) ∧
    ∃ hK : (K : Set S.completedLimit.carrier) ⊆ Metric.closedBall S.completedLimit.base (3/2),
      S.completedLimit.base ∈ K ∧
      (∀ j (x : (A j).boundedFiberSection), ∃ y : K,
        dist ((Q j).left ⟨x.val, Metric.mem_ball'.mpr
          (((A j).boundedFiberSection_dist_le x.val x.property).trans_lt (hs j))⟩)
          ((Q j).right ⟨y.val, Metric.mem_ball.mpr
            ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j) ∧
      (∀ j (y : K), ∃ x : (A j).boundedFiberSection,
        dist ((Q j).left ⟨x.val, Metric.mem_ball'.mpr
          (((A j).boundedFiberSection_dist_le x.val x.property).trans_lt (hs j))⟩)
          ((Q j).right ⟨y.val, Metric.mem_ball.mpr
            ((Metric.mem_closedBall.mp (hK y.property)).trans_lt (ht j))⟩) < ε j)

theorem exists_pointedCornerModels_tendsto_atTop
    {m k : ℕ} {δ H : ℝ}
    (hlarge : ∀ C : ℝ, ∃ A : PointedCornerModel m k δ H, C < A.weightedRatio) :
    ∃ A : ℕ → PointedCornerModel m k δ H,
      (∀ j : ℕ, (j : ℝ) < (A j).weightedRatio) ∧
      Tendsto (fun j => (A j).weightedRatio) atTop atTop := by
  classical
  choose A hA using fun j : ℕ => hlarge (j : ℝ)
  exact ⟨A, hA, tendsto_atTop_mono (fun j => (hA j).le)
    tendsto_natCast_atTop_atTop⟩

theorem exists_subseq_expandingCornerLimit
    {m k : ℕ} {δ H : ℝ} (hn : 1 ≤ m+k)
    (A : ℕ → PointedCornerModel m k δ H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ S : CompatiblePointedCompactSystem.{0},
      ∃ K : TopologicalSpace.NonemptyCompacts S.completedLimit.carrier,
        IsExpandingCornerLimit (fun j => A (φ j)) S K := by
  obtain ⟨φ, S, hφ, hproper, hgeo, hconv, s, t, ε, hsTop, htTop, hεpos,
    hεzero, hs, ht, Q, hQzero, K, hK, hbase, hforward, hbackward⟩ :=
    RiemannianMetric.exists_subseq_compact_openFiber_limit_in_expanding_realizations
      (fun j => (A j).metric) (fun j => (A j).connection) (fun j => (A j).complete) hn
      (fun j => (A j).sectional_lower) (fun j => (A j).joint)
      (fun j => (A j).joint_smooth.continuous) (fun j => (A j).domain)
      (fun j => (A j).value) (fun j => (A j).point) (ρ := 3/2) (by norm_num)
  exact ⟨φ, hφ, S, K, hproper, hgeo, hconv, s, t, ε, hsTop, htTop, hεpos,
    hεzero, hs, ht, Q, hQzero, hK, hbase, hforward, hbackward⟩




theorem IsExpandingCornerLimit.comp
    {m k : ℕ} {δ H : ℝ} {A : ℕ → PointedCornerModel m k δ H}
    {S : CompatiblePointedCompactSystem.{0}}
    {K : TopologicalSpace.NonemptyCompacts S.completedLimit.carrier}
    (h : IsExpandingCornerLimit A S K) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    IsExpandingCornerLimit (fun j => A (φ j)) S K := by
  obtain ⟨hp,hg,hc,s,t,ε,hsTop,htTop,hεp,hεzero,hs,ht,Q,hQ,hK,hbase,hf,hb⟩ := h
  have hc' : PointedGHConvergesUnbounded (fun j => (A (φ j)).basedSpace)
      S.completedLimit := by
    intro r hr
    obtain ⟨d,hd,hpos,⟨⟨C,hC⟩,hdist⟩⟩ := hc r hr
    exact ⟨fun j => d (φ j), hd.comp hφ, fun j => hpos (φ j),
      ⟨C,fun j => hC (φ j)⟩, hdist.comp hφ⟩
  exact ⟨hp,hg,hc',fun j => s (φ j),fun j => t (φ j),fun j => ε (φ j),
    hsTop.comp hφ,htTop.comp hφ,fun j => hεp (φ j),hεzero.comp hφ,
    (fun j => hs (φ j)),(fun j => ht (φ j)),(fun j => Q (φ j)),hQ.comp hφ,
    hK,hbase,(fun j => hf (φ j)),(fun j => hb (φ j))⟩


end PoincareConjecture
