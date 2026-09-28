import PoincareConjecture.Proofs.M47.LimitNoncollapseSourceCenters
import PoincareConjecture.Proofs.M47.LimitNoncollapsePhysicalTime
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoherence
import PoincareConjecture.Proofs.M04.ShiCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W history baseTime hbaseTime
  basePoint hPositive hDiverges

variable {J : Set ℝ} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges) J)

private local instance oldSlabTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance oldSlabCharts :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance oldSlabManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem limitFinite_preserved_future_bound_of_controlled
    (k : ℕ) {c Told R Bold eta : ℝ} (hTold : 0 < Told) (_hR : 0 < R)
    (hc : c ≤ -Told)
    (hsource : (G.limit.flow.metric 0).ball G.limit.base R ⊆ G.exhaustion.space k)
    (E : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
      (baseTime (G.subsequence k)) ((V).scale (G.subsequence k)) (Icc c 0)
      ((G.limit.flow.metric 0).ball G.limit.base R))
    (hzero : ∀ x ∈ (G.limit.flow.metric 0).ball G.limit.base R,
      E.forward 0 ⟨hc.trans (neg_nonpos.mpr hTold.le), le_rfl⟩ x =
        (history (G.subsequence k)).history.forward
          (baseTime (G.subsequence k) + 0 / (V).scale (G.subsequence k))
          (limitNoncollapse_physical_time_mem G k 0
            ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩)
          ((G.embedding k).forward 0
            ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩ x))
    (hquadratic : ∀ x ∈ (G.limit.flow.metric 0).ball G.limit.base R,
      ∀ v : TangentSpace (𝓡 3) x,
        (G.embedding k).pullbackInner 0
            ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩ x v v ≤
          2 * (G.limit.flow.metric 0).inner x v v)
    (C : ControlledBlowupCylinder V (G.subsequence k) (2 * R) Told Bold eta) :
    ∀ s (hs : s ∈ Icc (-Told) 0),
      ∀ x ∈ (G.limit.flow.metric 0).ball G.limit.base R,
        |((F (G.subsequence k)).connection
            (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).curvatureTensorNorm
          (E.forward s ⟨hc.trans hs.1, hs.2⟩ x)| ≤ Bold * (V).scale (G.subsequence k) ∧
        ((F (G.subsequence k)).connection
            (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).negativeCurvaturePart
          (E.forward s ⟨hc.trans hs.1, hs.2⟩ x) ≤ eta * (V).scale (G.subsequence k) := by
  have htime (s : ℝ) (hs : s ∈ Icc (-Told) 0) :
      baseTime (G.subsequence k) + s / (V).scale (G.subsequence k) ∈
        (history (G.subsequence k)).generalized.interval :=
    ((history (G.subsequence k)).generalized.slice_nonempty_iff _).mp
      ⟨C.embedding.forward s hs (basePoint (G.subsequence k))⟩
  have hball : IsOpen ((V).baseBall (G.subsequence k) (2 * R)) :=
    M04.initial_ball_isOpen _ _ _
  obtain ⟨Cp, hCp, _hCpMetric⟩ := (history (G.subsequence k)).cylinders_to_surgery
    (((V).flow (G.subsequence k)).slice ((V).base (G.subsequence k)).1)
    (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
    (Icc (-Told) 0) ((V).baseBall (G.subsequence k) (2 * R))
    ordConnected_Icc hball htime C.embedding
  intro s hs x hx
  let zeroG : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  let zeroC : (0 : ℝ) ∈ Icc (-Told) 0 := ⟨neg_nonpos.mpr hTold.le, le_rfl⟩
  obtain ⟨y, hy, hxy⟩ := limitNoncollapse_source_center_of_forward_bound
    (G.embedding k) (G.exhaustion.space_open k) zeroG (G.limit.flow.metric 0)
    G.limit.base x ((V).base (G.subsequence k)) (G.base_preserving k zeroG)
    hx hsource hquadratic
  have hy' : y ∈ (V).baseBall (G.subsequence k) (2 * R) := hy
  have hpoint := hxy.trans (C.zero_identity zeroC y hy').symm
  have hforward : (G.embedding k).forward 0 zeroG x =
      C.embedding.forward 0 zeroC y := eq_of_heq (Sigma.mk.inj hpoint).2
  have hterminal : E.forward 0 ⟨hc.trans (neg_nonpos.mpr hTold.le), le_rfl⟩ x =
      Cp.forward 0 zeroC y := by
    rw [hzero x hx, hCp 0 zeroC y hy', hforward]
  have hEq := terminalCommonInterval_physical_eq E Cp hs.2
    (fun _ hz => ⟨hc.trans (hs.1.trans hz.1), hz.2⟩)
    (fun _ hz => ⟨hs.1.trans hz.1, hz.2⟩) x hx y hy' hterminal
  rw [hEq, hCp s hs y hy',
    (history (G.subsequence k)).curvature_norm_pullback,
    (history (G.subsequence k)).negative_part_pullback]
  exact ⟨C.curvature_bound s hs y hy', C.negative_curvature_bound s hs y hy'⟩

end PoincareConjecture.M47
