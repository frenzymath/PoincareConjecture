import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Windows
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)

local instance (k : ℕ) : TopologicalSpace (S.term k).carrier.carrier :=
  (S.term k).carrier.topologicalSpace
local instance (k : ℕ) : MeasurableSpace (S.term k).carrier.carrier :=
  (S.term k).carrier.measurableSpace
local instance (k : ℕ) : BorelSpace (S.term k).carrier.carrier :=
  (S.term k).carrier.borelSpace
local instance (k : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin 3))
    (S.term k).carrier.carrier := (S.term k).carrier.chartedSpace
local instance (k : ℕ) : IsManifold (𝓡 3) ∞ (S.term k).carrier.carrier :=
  (S.term k).carrier.isManifold
local instance (k : ℕ) : T2Space (S.term k).carrier.carrier := (S.term k).carrier.t2Space
local instance (k : ℕ) : T3Space (S.term k).carrier.carrier := (S.term k).carrier.t3Space
local instance (k : ℕ) : SecondCountableTopology (S.term k).carrier.carrier :=
  (S.term k).carrier.secondCountable
local instance terminalSourceConnected (k : ℕ) : ConnectedSpace (S.term k).carrier.carrier :=
  (S.term k).connectedSpace

theorem allTime_curvatureDerivativeNorm_le
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (r : ℝ) (hr : 0 < r) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ, ∀ t : ℝ, t ≤ 0 →
      ∀ x ∈ ((S.term k).flow.flow.metric 0).ball (S.term k).base r,
        ((S.term k).flow.flow.connection t).curvatureDerivativeNorm m x ≤ D := by
  obtain ⟨C, hC, hbound⟩ := hcontrol (r + 1) (by linarith)
  let K := C + 1
  have hK : 0 < K := by dsimp [K]; linarith
  obtain ⟨D, hD, hShi⟩ := P.local_derivative_estimates m K K 1 hK hK (by norm_num)
  refine ⟨D, hD, ?_⟩
  intro k t ht x hx
  let B := S.term k
  change x ∈ (B.flow.flow.metric 0).ball B.base r at hx
  have hshift : (fun s : ℝ ↦ s + (t - 1)) '' Icc 0 1 ⊆ Iic 0 := by
    rintro _ ⟨s, hs, rfl⟩
    change s + (t - 1) ≤ 0
    linarith [hs.2]
  have hnontrivial : (Icc (0 : ℝ) 1).Nontrivial := by
    exact ⟨0, by norm_num, 1, by norm_num, by norm_num⟩
  let Ft := B.flow.flow.translate (t - 1) hshift ordConnected_Icc hnontrivial
  have hcompact : IsCompact (closure ((Ft.metric 0).ball x 1)) := by
    change IsCompact (closure ((B.flow.flow.metric (0 + (t - 1))).ball x 1))
    exact (B.flow.flow.metric (0 + (t - 1))).isCompact_closure_ball_of_metricComplete
      (B.flow.complete _ (by linarith)) x 1
  have hcurv : ∀ s ∈ Icc 0 1, ∀ y ∈ (Ft.metric 0).ball x 1,
      (Ft.connection s).curvatureTensorNorm y ≤ K := by
    intro s hs y hy
    have hyold : y ∈ (B.flow.flow.metric (t - 1)).ball x 1 := by
      simpa only [Ft, RicciFlow.translate, zero_add] using hy
    have hy0 := P.ball_monotone B.carrier.carrier B.flow (t - 1) 0
      (by linarith) le_rfl x 1 hyold
    have hybase : y ∈ (B.flow.flow.metric 0).ball B.base (r + 1) := by
      let := (B.flow.flow.metric 0).toMetricSpace
      have hx' : dist x B.base < r := by
        simpa only [← (B.flow.flow.metric 0).toMetricSpace_ball, Metric.mem_ball] using hx
      have hy' : dist y x < 1 := by
        simpa only [← (B.flow.flow.metric 0).toMetricSpace_ball, Metric.mem_ball] using hy0
      rw [← (B.flow.flow.metric 0).toMetricSpace_ball, Metric.mem_ball]
      linarith [dist_triangle y x B.base]
    have hle := hbound k (s + (t - 1)) (by linarith [hs.2]) y hybase
    exact (le_abs_self _).trans (hle.trans (by dsimp [K]; linarith))
  have hxhalf : x ∈ (Ft.metric 0).ball x (1 / 2) := by
    change (Ft.metric 0).edist x x < ENNReal.ofReal (1 / 2)
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    positivity
  have hder := hShi B.carrier.carrier 1 (by norm_num)
    (by rw [div_self hK.ne']) Ft x hcompact hcurv 1 (by norm_num) x hxhalf
  change (B.flow.flow.connection (1 + (t - 1))).curvatureDerivativeNorm m x ≤
    D / (1 : ℝ) ^ ((m : ℝ) / 2) at hder
  rw [show 1 + (t - 1) = t by ring, Real.one_rpow, div_one] at hder
  exact hder

end PoincareConjecture.NormalizedKappaSolutionSequence
