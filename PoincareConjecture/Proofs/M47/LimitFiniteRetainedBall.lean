import PoincareConjecture.Proofs.M47.LimitFiniteRetainedCylinder
import PoincareConjecture.Proofs.M47.LimitFinitePhysicalCoherence
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCapture
import PoincareConjecture.Proofs.M47.LimitNoncollapseMetric
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Proofs.M04.ShiCarrier
import PoincareConjecture.Proofs.M36.MetricComparison

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

variable {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
  (blowupBackwardInterval H))

private local instance retainedBallTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance retainedBallCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance retainedBallManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

variable (sigma eta : ℕ → ℕ)

local notation "X" => G.limit.sliceCarrier.carrier
local notation "q" => (fun k => sigma (eta k))
local notation "n" => (fun k => G.subsequence (q k))
local notation "Q" => (fun k => GeneralizedBlowupSequence.scale
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
  (G.subsequence (sigma (eta k))))
local notation "c" => (-H.toReal)
local notation "g" => (G.limit.flow.metric 0)

theorem limitFinite_eventually_retained_terminal_ball
    (hsigma : StrictMono sigma) (heta : StrictMono eta)
    (j : ℕ → ℕ) (hj : ∀ m, closure (G.exhaustion.space m) ⊆ G.exhaustion.space (j m))
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X
      ((F (n k)).slice (baseTime (n k) + c / Q k)).carrier ∞)
    (hrow : ∀ m, ∀ᶠ k : ℕ in atTop,
      ∃ b, ∃ hb : b ≤ c,
        ∃ e : SurgeryFlowCylinder (F (n k)) G.limit.sliceCarrier
            (baseTime (n k)) (Q k) (Icc b 0) (G.exhaustion.space (j m)),
          EqOn (psi k) (e.forward c ⟨hb, neg_nonpos.mpr ENNReal.toReal_nonneg⟩)
            (G.exhaustion.space (j m)) ∧
          ∀ hzero : (0 : ℝ) ∈ Icc b 0, ∀ x ∈ G.exhaustion.space (j m),
            e.forward 0 hzero x = (history (n k)).history.forward
              (baseTime (n k) + 0 / Q k)
              (limitNoncollapse_physical_time_mem G (q k) 0
                ⟨neg_nonpos.mpr (G.exhaustion.time_pos (q k)).le, le_rfl⟩)
              ((G.embedding (q k)).forward 0
                ⟨neg_nonpos.mpr (G.exhaustion.time_pos (q k)).le, le_rfl⟩ x))
    (L : ℝ)
    (hscalar : ∀ K : Set X, IsCompact K → ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ K, ((F (n k)).connection (baseTime (n k) + c / Q k)).scalarCurvature
        (psi k x) ≤ L * Q k)
    (R : ℝ) (hR : 0 < R) :
    let U := (g).ball G.limit.base R
    ∀ᶠ k : ℕ in atTop, U ⊆ G.exhaustion.space (q k) ∧
      ∃ e0 : SurgeryFlowCylinder (F (n k)) G.limit.sliceCarrier
          (baseTime (n k)) (Q k) (Icc c 0) U,
        EqOn (psi k) (e0.forward c ⟨le_rfl, neg_nonpos.mpr ENNReal.toReal_nonneg⟩) U ∧
        (∀ s (hs : s ∈ Icc c 0) (hsG : s ∈ Icc (-G.exhaustion.time (q k)) 0),
          ∀ x ∈ U, e0.forward s hs x = (history (n k)).history.forward
            (baseTime (n k) + s / Q k)
            (limitNoncollapse_physical_time_mem G (q k) s hsG)
            ((G.embedding (q k)).forward s hsG x)) ∧
        (∀ s (hs : s ∈ Icc c 0) (hsG : s ∈ Icc (-G.exhaustion.time (q k)) 0),
          ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
            e0.pullbackInner s hs x v w = (G.embedding (q k)).pullbackInner s hsG x v w) ∧
        (∀ x ∈ U,
          ((F (n k)).connection (baseTime (n k) + c / Q k)).scalarCurvature
            (e0.forward c ⟨le_rfl, neg_nonpos.mpr ENNReal.toReal_nonneg⟩ x) ≤ L * Q k) ∧
        (∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
          e0.pullbackInner 0 ⟨neg_nonpos.mpr ENNReal.toReal_nonneg, le_rfl⟩ x v v ≤
            2 * (g).inner x v v) ∧
        ((⟨baseTime (n k) + 0 / Q k,
            e0.forward 0 ⟨neg_nonpos.mpr ENNReal.toReal_nonneg, le_rfl⟩ G.limit.base⟩ :
            Σ t, ((F (n k)).slice t).carrier) =
          ⟨baseTime (n k), (history (n k)).history.forward
            (baseTime (n k)) (hbaseTime (n k)) (basePoint (n k))⟩) := by
  intro U
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  have hc : c ≤ 0 := neg_nonpos.mpr ENNReal.toReal_nonneg
  have hU : IsOpen U := M04.initial_ball_isOpen g G.limit.base R
  have hcompact : IsCompact (closure U) := terminalCommonInterval_compact_ball_closure
    g (G.limit.complete 0 G.limit.zero_mem) G.limit.base R
  obtain ⟨m, hm⟩ := hcompact.elim_directed_cover G.exhaustion.space
    G.exhaustion.space_open (by rw [G.exhaustion.space_covers]; exact subset_univ _)
    G.exhaustion.space_increasing.directed_le
  have hUrow : U ⊆ G.exhaustion.space (j m) :=
    subset_closure.trans (hm.trans (subset_closure.trans (hj m)))
  have hzero : ∀ k, (0 : ℝ) ∈ Icc (-G.exhaustion.time (q k)) 0 :=
    fun k => ⟨neg_nonpos.mpr (G.exhaustion.time_pos (q k)).le, le_rfl⟩
  have hmetric := (hsigma.comp heta).tendsto_atTop.eventually
    (limitNoncollapse_compact_inner_zero G hcompact)
  filter_upwards [hrow m, hscalar (closure U) hcompact, hmetric] with k hk hsk hmk
  obtain ⟨b, hb, e, hpsi, hezero⟩ := hk
  have hUk : U ⊆ G.exhaustion.space (q k) := subset_closure.trans hmk.1
  let e0 := e.restrict (Icc_subset_Icc hb le_rfl) ordConnected_Icc hUrow
  have he0 : ∀ x ∈ U, e0.forward 0 ⟨hc, le_rfl⟩ x =
      (history (n k)).history.forward (baseTime (n k) + 0 / Q k)
        (limitNoncollapse_physical_time_mem G (q k) 0 (hzero k))
        ((G.embedding (q k)).forward 0 (hzero k) x) := by
    intro x hx
    exact hezero _ x (hUrow hx)
  obtain ⟨f, hfmap, hfmetric⟩ := (history (n k)).cylinders_to_surgery
    G.limit.sliceCarrier (baseTime (n k)) (Q k) (Icc (-G.exhaustion.time (q k)) 0)
    (G.exhaustion.space (q k)) ordConnected_Icc (G.exhaustion.space_open (q k))
    (fun s hs => limitNoncollapse_physical_time_mem G (q k) s hs) (G.embedding (q k))
  have heq0 : ∀ x ∈ U, e0.forward 0 ⟨hc, le_rfl⟩ x = f.forward 0 (hzero k) x := by
    intro x hx
    exact (he0 x hx).trans (hfmap 0 (hzero k) x (hUk hx)).symm
  have hmap : ∀ s (hs : s ∈ Icc c 0) (hsG : s ∈ Icc (-G.exhaustion.time (q k)) 0),
      ∀ x ∈ U, e0.forward s hs x = (history (n k)).history.forward
        (baseTime (n k) + s / Q k)
        (limitNoncollapse_physical_time_mem G (q k) s hsG)
        ((G.embedding (q k)).forward s hsG x) := by
    intro s hs hsG x hx
    exact (terminalCommonInterval_physical_eq e0 f hs.2
      (Icc_subset_Icc hs.1 le_rfl) (Icc_subset_Icc hsG.1 le_rfl)
      x hx x (hUk hx) (heq0 x hx)).trans (hfmap s hsG x (hUk hx))
  have hinner : ∀ s (hs : s ∈ Icc c 0) (hsG : s ∈ Icc (-G.exhaustion.time (q k)) 0),
      ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
        e0.pullbackInner s hs x v w = (G.embedding (q k)).pullbackInner s hsG x v w := by
    intro s hs hsG x hx v w
    exact (limitFinite_physical_pullback_eq e0 f hU (G.exhaustion.space_open (q k))
      hs.2 (Icc_subset_Icc hs.1 le_rfl) (Icc_subset_Icc hsG.1 le_rfl)
      (fun y hy => heq0 y hy.1) ⟨hx, hUk hx⟩ v w).trans
        (hfmetric s hsG x (hUk hx) v w)
  refine ⟨hUk, e0, (fun x hx => hpsi (hUrow hx)), hmap, hinner, ?_, ?_, ?_⟩
  · intro x hx
    change ((F (n k)).connection (baseTime (n k) + c / Q k)).scalarCurvature
      (e.forward c _ x) ≤ L * Q k
    rw [← hpsi (hUrow hx)]
    exact hsk x (subset_closure hx)
  · intro x hx v
    rw [hinner 0 ⟨hc, le_rfl⟩ (hzero k) x hx v v]
    exact (hmk.2 x (subset_closure hx) v).2
  · have ho : G.limit.base ∈ U := by
      change (g).edist G.limit.base G.limit.base < ENNReal.ofReal R
      rw [M36.metric_edist_self]
      exact ENNReal.ofReal_pos.mpr hR
    have hp := limitCanonicalPhysicalChart_point_identity (G.embedding (q k))
      (G.exhaustion.space_open (q k)) (history (n k)).history
      0 (hzero k) (limitNoncollapse_physical_time_mem G (q k) 0 (hzero k))
      G.limit.base ((V).base (n k)) (hbaseTime (n k)) (G.base_preserving (q k) (hzero k))
    change (⟨baseTime (n k) + 0 / Q k,
      (history (n k)).history.forward (baseTime (n k) + 0 / Q k)
        (limitNoncollapse_physical_time_mem G (q k) 0 (hzero k))
        ((G.embedding (q k)).forward 0 (hzero k) G.limit.base)⟩ :
      Σ t, ((F (n k)).slice t).carrier) = _ at hp
    rw [← he0 G.limit.base ho] at hp
    exact hp

end PoincareConjecture.M47
