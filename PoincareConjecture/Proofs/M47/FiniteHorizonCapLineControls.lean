import PoincareConjecture.Proofs.M47.LimitFiniteRetainedBall
import PoincareConjecture.Proofs.M47.LimitFiniteOldSlabBound
import PoincareConjecture.Proofs.M47.FiniteHorizonCapLineScalar
import PoincareConjecture.Statements.M47CanonicalInduction

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

private local instance capLineControlsTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance capLineControlsCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance capLineControlsManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

variable (sigma etaIndex : ℕ → ℕ)

local notation "X" => G.limit.sliceCarrier.carrier
local notation "qIndex" => (fun k => sigma (etaIndex k))
local notation "n" => (fun k => G.subsequence (sigma (etaIndex k)))
local notation "Q" => (fun k => GeneralizedBlowupSequence.scale
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
  (G.subsequence (sigma (etaIndex k))))
local notation "c" => (-H.toReal)
local notation "g" => (G.limit.flow.metric 0)

theorem finiteHorizon_eventually_cap_line_bound
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (controls : M30GeometricLongControls V H) (hfinite : H ≠ ⊤)
    (hsigma : StrictMono sigma) (hetaIndex : StrictMono etaIndex)
    (p : ℕ → SurgeryParameterPrefix S.constants) (O : ∀ k, SurgeryObservation (F k))
    (hInitial : ∀ k, (F k).standard_initial = S.setup.standard_initial)
    (hConstants : ∀ k, (F k).local_constants = S.constants)
    (hC : ∀ k, (F k).parameters.C = S.setup.C)
    (hBase : ∀ k, baseTime k ∈ Ico (surgeryEpochStart (p k).i) (O k).H)
    (hPinched : ∀ k, SurgeryFlowPinched (F k))
    (rNext : ℕ → ℝ) (hThreshold : ∀ k, (rNext k)⁻¹ ^ 2 ≤ (V).scale k)
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (rNext k))
    (hOverlap : ∀ k, ∀ t ∈ surgeryObservationInterval (O k) ∩
        Ico (surgeryEpochStart ((p k).i - 1)) (O k).H,
      (F k).parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X
      ((F (n k)).slice (baseTime (n k) + c / Q k)).carrier ∞)
    (L : ℝ) (hL : 1 ≤ L)
    (hballs : ∀ R : ℝ, 0 < R →
      let U := (g).ball G.limit.base R
      ∀ᶠ k : ℕ in atTop, U ⊆ G.exhaustion.space (qIndex k) ∧
        ∃ e0 : SurgeryFlowCylinder (F (n k)) G.limit.sliceCarrier
            (baseTime (n k)) (Q k) (Icc c 0) U,
          EqOn (psi k) (e0.forward c ⟨le_rfl, neg_nonpos.mpr ENNReal.toReal_nonneg⟩) U ∧
          (∀ s (hs : s ∈ Icc c 0) (hsG : s ∈ Icc (-G.exhaustion.time (qIndex k)) 0),
            ∀ x ∈ U, e0.forward s hs x = (history (n k)).history.forward
              (baseTime (n k) + s / Q k)
              (limitNoncollapse_physical_time_mem G (qIndex k) s hsG)
              ((G.embedding (qIndex k)).forward s hsG x)) ∧
          (∀ s (hs : s ∈ Icc c 0) (hsG : s ∈ Icc (-G.exhaustion.time (qIndex k)) 0),
            ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
              e0.pullbackInner s hs x v w = (G.embedding (qIndex k)).pullbackInner s hsG x v w) ∧
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
              (baseTime (n k)) (hbaseTime (n k)) (basePoint (n k))⟩)) :
    ∃ d Bold : ℝ, 0 < d ∧ d ≤ H.toReal / 4 ∧
      64 * blowupAnalyticConstant S B * L * (4 * d) ≤ 1 ∧ 0 ≤ Bold ∧
      ∀ R : ℝ, 0 < R →
        let U := (g).ball G.limit.base R
        ∀ᶠ k : ℕ in atTop,
          ∀ (a : ℝ) (_ha : a ∈ Icc (c - 4 * d) c),
          ∀ E : SurgeryFlowCylinder (F (n k)) G.limit.sliceCarrier
              (baseTime (n k)) (Q k) (Icc a 0) U,
          (∀ hz : (0 : ℝ) ∈ Icc a 0, ∀ x ∈ U,
            E.forward 0 hz x = (history (n k)).history.forward
              (baseTime (n k) + 0 / Q k)
              (limitNoncollapse_physical_time_mem G (qIndex k) 0
                ⟨neg_nonpos.mpr (G.exhaustion.time_pos (qIndex k)).le, le_rfl⟩)
              ((G.embedding (qIndex k)).forward 0
                ⟨neg_nonpos.mpr (G.exhaustion.time_pos (qIndex k)).le, le_rfl⟩ x)) →
          ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
            ((F (n k)).connection (baseTime (n k) + s / Q k)).scalarCurvature
              (E.forward s hs x) ≤ max (4 * L) (3 * Bold) * Q k := by
  have hT : 0 < H.toReal := ENNReal.toReal_pos controls.horizon_pos.ne' hfinite
  let Aanalytic := blowupAnalyticConstant S B
  have hAanalytic : 0 < Aanalytic := blowupAnalyticConstant_pos S B
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  let d := min (H.toReal / 4) (1 / (256 * Aanalytic * L))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdT : d ≤ H.toReal / 4 := min_le_left _ _
  have hdtime : d ≤ 1 / (256 * Aanalytic * L) := min_le_right _ _
  have hshort : 64 * blowupAnalyticConstant S B * L * (4 * d) ≤ 1 := by
    have hprod : 0 < 256 * Aanalytic * L := by positivity
    have h := (le_div_iff₀ hprod).mp hdtime
    change 64 * Aanalytic * L * (4 * d) ≤ 1
    nlinarith only [h]
  let Told := H.toReal - d
  have hTold : 0 < Told := by dsimp only [Told]; linarith only [hT, hdT]
  have hToldH : ENNReal.ofReal Told < H := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal hTold.le hfinite).mpr
    dsimp only [Told]
    linarith only [hd]
  obtain ⟨Bold, hBold, oldControls⟩ := controls.cylinders Told hTold hToldH
  let window := H.toReal + 4 * d
  have hwindow : 0 ≤ window := by dsimp only [window]; positivity
  have hcneg : c < 0 := neg_neg_of_pos hT
  have hc2 : c + 2 * d ≤ 0 := by linarith only [hT, hdT]
  have hcOld : c ≤ -Told := by dsimp only [Told]; linarith only [hd]
  have hbuffer : -window ≤ c - 4 * d := by dsimp only [window]; linarith
  have hn : StrictMono n := G.subsequence_strictMono.comp (hsigma.comp hetaIndex)
  have hQtail := (V).scalar_diverges.comp hn.tendsto_atTop
  let zeroG : ∀ k, (0 : ℝ) ∈ Icc (-G.exhaustion.time (qIndex k)) 0 :=
    fun k => ⟨neg_nonpos.mpr (G.exhaustion.time_pos (qIndex k)).le, le_rfl⟩
  let zero0 : (0 : ℝ) ∈ Icc c 0 := ⟨hcneg.le, le_rfl⟩
  refine ⟨d, Bold, hd, hdT, hshort, hBold, ?_⟩
  intro R hR
  let U := (g).ball G.limit.base R
  have hcontrolled := hn.tendsto_atTop.eventually
    (oldControls (2 * R) (mul_pos two_pos hR) 1 zero_lt_one)
  filter_upwards [hballs R hR, hcontrolled,
    hQtail.eventually (eventually_ge_atTop (64 * (window + 1))),
    hQtail.eventually (eventually_ge_atTop B.curvature_threshold)]
    with k hk hcontrolled hscale hlarge
  obtain ⟨hsource, e0, _hpsi, hmap, hinner, hscalar, hzeroInner, _hpoint⟩ := hk
  obtain ⟨Ck⟩ := hcontrolled
  intro a ha E hzero
  have ha0 : a ≤ 0 := ha.2.trans hcneg.le
  have hEndpoint : ∀ x ∈ U,
      ((F (n k)).connection (baseTime (n k) + c / Q k)).scalarCurvature
        (E.forward c ⟨ha.2, hcneg.le⟩ x) ≤ L * Q k := by
    intro x hx
    have hterminal : E.forward 0 ⟨ha0, le_rfl⟩ x = e0.forward 0 zero0 x :=
      (hzero ⟨ha0, le_rfl⟩ x hx).trans (hmap 0 zero0 (zeroG k) x hx).symm
    have heq := terminalCommonInterval_physical_eq E e0 hcneg.le
      (fun _ hs => ⟨ha.2.trans hs.1, hs.2⟩) (Subset.refl _) x hx x hx hterminal
    rw [heq]
    exact hscalar x hx
  have hquadratic : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      (G.embedding (qIndex k)).pullbackInner 0 (zeroG k) x v v ≤
        2 * (g).inner x v v := by
    intro x hx v
    rw [← hinner 0 zero0 (zeroG k) x hx v v]
    exact hzeroInner x hx v
  have hOld0 := limitFinite_preserved_future_bound_of_controlled F W history baseTime
    hbaseTime basePoint hPositive hDiverges G (qIndex k) hTold hR (ha.2.trans hcOld)
    hsource E (hzero _) hquadratic Ck
  have hOld : ∀ s (hs : s ∈ Icc (c + d) 0), ∀ x ∈ U,
      |((F (n k)).connection (baseTime (n k) + s / Q k)).curvatureTensorNorm
        (E.forward s ⟨by linarith only [hs.1, ha.2, hd], hs.2⟩ x)| ≤ Bold * Q k := by
    intro s hs x hx
    have hsOld : s ∈ Icc (-Told) 0 := by
      dsimp only [Told]
      exact ⟨by linarith only [hs.1], hs.2⟩
    exact (hOld0 s hsOld x hx).1
  have hpast : SurgeryCanonicalOn (F (n k))
      (surgeryObservationInterval (O (n k)) ∩ Iio (baseTime (n k))) (rNext (n k)) :=
    fun t ht => hEarlier (n k) t ⟨ht.1.1, ht.2⟩
  have bound := finiteHorizon_cap_cylinder_scalar_bound S B (p (n k)) (O (n k))
    (hInitial (n k)) (hConstants (n k)) (hC (n k)) (hBase (n k)) hwindow hscale hlarge
    (hThreshold (n k)) (hPinched (n k)) hpast (hOverlap (n k))
    ⟨P.m04, P.m13.ordinary_flow⟩ («Q» := Q k) (shift := 0) (a := a)
    («c» := c) (d := d) (L := L) (Bold := Bold) (C := G.limit.sliceCarrier) (U := U)
  rw [zero_div, add_zero, zero_add] at bound
  exact bound E le_rfl hd hc2 ha hbuffer hL hshort hEndpoint hOld

end PoincareConjecture.M47
