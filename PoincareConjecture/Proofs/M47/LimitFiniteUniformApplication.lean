import PoincareConjecture.Proofs.M47.LimitFiniteRetainedBall
import PoincareConjecture.Proofs.M47.LimitFiniteOldSlabBound
import PoincareConjecture.Proofs.M47.LimitFiniteUniformSearch
import PoincareConjecture.Proofs.M47.LimitFiniteUniformCapExclusion

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

private local instance uniformApplicationTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance uniformApplicationCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance uniformApplicationManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
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

theorem limitFinite_eventually_uniform_endpoint_extension
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
    (hbad : ∀ k, ¬ SurgeryCanonicalControl (F k) (baseTime k)
      ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))
      (F k).parameters.epsilon (F k).parameters.C)
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
              (baseTime (n k)) (hbaseTime (n k)) (basePoint (n k))⟩))
    (capBudget : ∀ j : ℕ, ∀ᶠ k : ℕ in atTop,
      ∀ (C0 : GeneralizedSliceCarrier.{u}) {U0 : Set C0.carrier}, IsOpen U0 →
      ∀ {a : ℝ} (ha : a ∈ Ico (-((j : ℝ) + 1)) 0),
      ∀ e : SurgeryFlowCylinder (F (n k)) C0 (baseTime (n k)) (Q k) (Icc a 0) U0,
        (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U0,
          ((F (n k)).connection (baseTime (n k) + s / Q k)).scalarCurvature
            (e.forward s hs x) ≤ ((j : ℝ) + 1) * Q k) →
        let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
        let zero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.2.le, le_rfl⟩
        let tbirth := baseTime (n k) + a / Q k
        ∀ (hEvent : tbirth ∈ (F (n k)).surgery_times),
        ∀ [Nonempty ((F (n k)).slice tbirth).carrier],
        ∀ (i : Fin ((F (n k)).event tbirth hEvent).cap_count) (contact : C0.carrier),
          contact ∈ U0 →
          e.forward a bottom contact ∈ (((F (n k)).event tbirth hEvent).caps i).carrier →
          (∀ x ∈ U0, ((F (n k)).metric tbirth).edist
            (e.forward a bottom contact) (e.forward a bottom x) ≤
              ENNReal.ofReal (((j : ℝ) + 1) / Real.sqrt (Q k))) →
          ∀ y ∈ U0,
            ((F (n k)).connection (baseTime (n k) + 0 / Q k)).scalarCurvature
              (e.forward 0 zero y) = Q k →
            SurgeryCanonicalControl (F (n k)) (baseTime (n k) + 0 / Q k)
              (e.forward 0 zero y) (F (n k)).parameters.epsilon (F (n k)).parameters.C) :
    ∃ d Bold : ℝ, 0 < d ∧ d ≤ H.toReal / 4 ∧
      64 * blowupAnalyticConstant S B * L * (4 * d) ≤ 1 ∧ 0 ≤ Bold ∧
      let Bplus := max (13 * max (4 * L) 1) Bold
      ∀ R : ℝ, 0 < R → ∀ err : ℝ, 0 < err →
        let U := (g).ball G.limit.base R
        ∀ᶠ k : ℕ in atTop,
          ∃ b, ∃ hb : b ∈ Icc (-(H.toReal + 4 * d)) c,
            ∃ E : SurgeryFlowCylinder (F (n k)) G.limit.sliceCarrier
                (baseTime (n k)) (Q k) (Icc b 0) U,
              U ⊆ G.exhaustion.space (qIndex k) ∧
              (∀ hzero : (0 : ℝ) ∈ Icc b 0, ∀ x ∈ U,
                E.forward 0 hzero x = (history (n k)).history.forward
                  (baseTime (n k) + 0 / Q k)
                  (limitNoncollapse_physical_time_mem G (qIndex k) 0
                    ⟨neg_nonpos.mpr (G.exhaustion.time_pos (qIndex k)).le, le_rfl⟩)
                  ((G.embedding (qIndex k)).forward 0
                    ⟨neg_nonpos.mpr (G.exhaustion.time_pos (qIndex k)).le, le_rfl⟩ x)) ∧
              (∀ hc : c ∈ Icc b 0, EqOn (psi k) (E.forward c hc) U) ∧
              (∀ s (_hs0 : s ∈ Icc c 0) (hsE : s ∈ Icc b 0)
                (hsG : s ∈ Icc (-G.exhaustion.time (qIndex k)) 0),
                ∀ x ∈ U, E.forward s hsE x = (history (n k)).history.forward
                  (baseTime (n k) + s / Q k)
                  (limitNoncollapse_physical_time_mem G (qIndex k) s hsG)
                  ((G.embedding (qIndex k)).forward s hsG x)) ∧
              (∀ s (_hs0 : s ∈ Icc c 0) (hsE : s ∈ Icc b 0)
                (hsG : s ∈ Icc (-G.exhaustion.time (qIndex k)) 0),
                ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
                  E.pullbackInner s hsE x v w =
                    (G.embedding (qIndex k)).pullbackInner s hsG x v w) ∧
              (∀ hc : c ∈ Icc b 0, ∀ x ∈ U,
                ((F (n k)).connection (baseTime (n k) + c / Q k)).scalarCurvature
                  (E.forward c hc x) ≤ L * Q k) ∧
              (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U,
                |((F (n k)).connection (baseTime (n k) + s / Q k)).curvatureTensorNorm
                  (E.forward s hs x)| ≤ Bplus * Q k ∧
                ((F (n k)).connection (baseTime (n k) + s / Q k)).negativeCurvaturePart
                  (E.forward s hs x) ≤ err * Q k) ∧
              (∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
                E.pullbackInner 0 ⟨hb.2.trans (neg_nonpos.mpr ENNReal.toReal_nonneg), le_rfl⟩
                  x v v ≤ 2 * (g).inner x v v) ∧
              ((⟨baseTime (n k) + 0 / Q k,
                  E.forward 0 ⟨hb.2.trans (neg_nonpos.mpr ENNReal.toReal_nonneg), le_rfl⟩
                    G.limit.base⟩ : Σ t, ((F (n k)).slice t).carrier) =
                ⟨baseTime (n k), (history (n k)).history.forward
                  (baseTime (n k)) (hbaseTime (n k)) (basePoint (n k))⟩) ∧
              b < -(H.toReal + 2 * d) := by
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
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
  let Bplus := max (13 * max (4 * L) 1) Bold
  have hBplus : 0 ≤ Bplus := hBold.trans (le_max_right _ _)
  let window := H.toReal + 4 * d
  have hwindow : 0 ≤ window := by dsimp only [window]; positivity
  have hcneg : c < 0 := neg_neg_of_pos hT
  have hc2 : c + 2 * d ≤ 0 := by linarith only [hT, hdT]
  have hcOld : c ≤ -Told := by dsimp only [Told]; linarith only [hd]
  have hbuffer : -window ≤ c - 4 * d := by dsimp only [window]; linarith
  have hn : StrictMono n := G.subsequence_strictMono.comp (hsigma.comp hetaIndex)
  have hQtail := (V).scalar_diverges.comp hn.tendsto_atTop
  have hQ (k : ℕ) : 0 < Q k := (V).base_scalar_pos (n k)
  let zeroG : ∀ k, (0 : ℝ) ∈ Icc (-G.exhaustion.time (qIndex k)) 0 :=
    fun k => ⟨neg_nonpos.mpr (G.exhaustion.time_pos (qIndex k)).le, le_rfl⟩
  let zero0 : (0 : ℝ) ∈ Icc c 0 := ⟨hcneg.le, le_rfl⟩
  let bottom0 : c ∈ Icc c 0 := ⟨le_rfl, hcneg.le⟩
  refine ⟨d, Bold, hd, hdT, hshort, hBold, ?_⟩
  change ∀ R : ℝ, 0 < R → ∀ err : ℝ, 0 < err → _
  intro R hR
  let U := (g).ball G.limit.base R
  have hU : IsOpen U := M04.initial_ball_isOpen g G.limit.base R
  have hbaseU : G.limit.base ∈ U := by
    change (g).edist G.limit.base G.limit.base < ENNReal.ofReal R
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hR
  let Retain : ∀ k b, SurgeryFlowCylinder (F (n k)) G.limit.sliceCarrier
      (baseTime (n k)) (Q k) (Icc b 0) U → Prop := fun k b E =>
    U ⊆ G.exhaustion.space (qIndex k) ∧
    (∀ hzero : (0 : ℝ) ∈ Icc b 0, ∀ x ∈ U,
      E.forward 0 hzero x = (history (n k)).history.forward
        (baseTime (n k) + 0 / Q k)
        (limitNoncollapse_physical_time_mem G (qIndex k) 0 (zeroG k))
        ((G.embedding (qIndex k)).forward 0 (zeroG k) x)) ∧
    (∀ hc : c ∈ Icc b 0, EqOn (psi k) (E.forward c hc) U) ∧
    (∀ s (_hs0 : s ∈ Icc c 0) (hsE : s ∈ Icc b 0)
      (hsG : s ∈ Icc (-G.exhaustion.time (qIndex k)) 0),
      ∀ x ∈ U, E.forward s hsE x = (history (n k)).history.forward
        (baseTime (n k) + s / Q k) (limitNoncollapse_physical_time_mem G (qIndex k) s hsG)
        ((G.embedding (qIndex k)).forward s hsG x)) ∧
    (∀ s (_hs0 : s ∈ Icc c 0) (hsE : s ∈ Icc b 0)
      (hsG : s ∈ Icc (-G.exhaustion.time (qIndex k)) 0),
      ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
        E.pullbackInner s hsE x v w = (G.embedding (qIndex k)).pullbackInner s hsG x v w) ∧
    ∀ hc : c ∈ Icc b 0, ∀ x ∈ U,
      ((F (n k)).connection (baseTime (n k) + c / Q k)).scalarCurvature
        (E.forward c hc x) ≤ L * Q k
  have hsearch : ∀ err : ℝ, 0 < err → ∀ᶠ k : ℕ in atTop,
      ∃ b, ∃ hb : b ∈ Icc (c - 4 * d) c,
        ∃ E : SurgeryFlowCylinder (F (n k)) G.limit.sliceCarrier
            (baseTime (n k)) (Q k) (Icc b 0) U,
          Retain k b E ∧
          (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U,
            |((F (n k)).connection (baseTime (n k) + s / Q k)).curvatureTensorNorm
              (E.forward s hs x)| ≤ Bplus * Q k ∧
            ((F (n k)).connection (baseTime (n k) + s / Q k)).negativeCurvaturePart
              (E.forward s hs x) ≤ err * Q k) ∧
          (∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
            E.pullbackInner 0 ⟨hb.2.trans hcneg.le, le_rfl⟩ x v v ≤ 2 * (g).inner x v v) ∧
          ((⟨baseTime (n k) + 0 / Q k,
              E.forward 0 ⟨hb.2.trans hcneg.le, le_rfl⟩ G.limit.base⟩ :
              Σ t, ((F (n k)).slice t).carrier) =
            ⟨baseTime (n k), (history (n k)).history.forward
              (baseTime (n k)) (hbaseTime (n k)) (basePoint (n k))⟩) ∧
          (b < c - 2 * d ∨
            ∃ hEvent : baseTime (n k) + b / Q k ∈ (F (n k)).surgery_times,
              ∀ [Nonempty ((F (n k)).slice (baseTime (n k) + b / Q k)).carrier],
                ∃ i : Fin ((F (n k)).event (baseTime (n k) + b / Q k) hEvent).cap_count,
                  Set.Nonempty (E.forward b ⟨le_rfl, hb.2.trans hcneg.le⟩ '' U ∩
                    (((F (n k)).event (baseTime (n k) + b / Q k) hEvent).caps i).carrier)) := by
    intro err herr
    have hcontrolled := hn.tendsto_atTop.eventually
      (oldControls (2 * R) (mul_pos two_pos hR) err herr)
    filter_upwards [hballs R hR, hcontrolled,
      hQtail.eventually (eventually_ge_atTop (64 * (window + 1))),
      hQtail.eventually (eventually_ge_atTop B.curvature_threshold),
      hQtail.eventually (eventually_ge_atTop (blowupPinchingThreshold (4 * L) err))]
      with k hk hcontrolled hscale hlarge hpinching
    obtain ⟨hsource, e0, hpsi, hmap, hinner, hscalar, hzeroInner, hpoint⟩ := hk
    obtain ⟨Ck⟩ := hcontrolled
    have hquadratic : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
        (G.embedding (qIndex k)).pullbackInner 0 (zeroG k) x v v ≤
          2 * (g).inner x v v := by
      intro x hx v
      rw [← hinner 0 zero0 (zeroG k) x hx v v]
      exact hzeroInner x hx v
    have hOld0 := limitFinite_preserved_future_bound_of_controlled F W history baseTime
      hbaseTime basePoint hPositive hDiverges G (qIndex k) hTold hR hcOld hsource e0
      (hmap 0 zero0 (zeroG k)) hquadratic Ck
    have hOld : ∀ s (hs : s ∈ Icc (c + d) 0), ∀ x ∈ U,
        |((F (n k)).connection (baseTime (n k) + s / Q k)).curvatureTensorNorm
          (e0.forward s ⟨by linarith only [hs.1, hd], hs.2⟩ x)| ≤ Bold * Q k ∧
        ((F (n k)).connection (baseTime (n k) + s / Q k)).negativeCurvaturePart
          (e0.forward s ⟨by linarith only [hs.1, hd], hs.2⟩ x) ≤ err * Q k := by
      intro s hs x hx
      have hsOld : s ∈ Icc (-Told) 0 := by
        dsimp only [Told]
        exact ⟨by linarith only [hs.1], hs.2⟩
      exact hOld0 s hsOld x hx
    have hpast : SurgeryCanonicalOn (F (n k))
        (surgeryObservationInterval (O (n k)) ∩ Iio (baseTime (n k))) (rNext (n k)) :=
      fun t ht => hEarlier (n k) t ⟨ht.1.1, ht.2⟩
    have search := limitFinite_exists_uniform_preserved_search S B (p (n k)) (O (n k))
      (hInitial (n k)) (hConstants (n k)) (hC (n k)) (hBase (n k)) hwindow hscale hlarge
      (hThreshold (n k)) (hPinched (n k)) hpast (hOverlap (n k)) P.toM46
      («Q» := Q k) (shift := 0) («c» := c) (d := d) (L := L) (Bold := Bold) (eta := err)
      (C := G.limit.sliceCarrier) (U := U)
    rw [zero_div, add_zero, zero_add] at search
    obtain ⟨b, hb, E, hfuture, hbound, hstop⟩ := search e0 le_rfl hd hc2 hbuffer hL hshort
      hU ⟨G.limit.base, hbaseU⟩ hscalar herr hpinching hOld
    have hfutureMetric (s : ℝ) (hs : s ∈ Icc c 0) (hsE : s ∈ Icc b 0)
        (x : X) (v w : TangentSpace (𝓡 3) x) :
        E.pullbackInner s hsE x v w = e0.pullbackInner s hs x v w := by
      have hfun : E.forward s hsE = e0.forward s hs := funext (hfuture s hs hsE)
      unfold SurgeryFlowCylinder.pullbackInner
      rw [hfun]
    have hretain : Retain k b E := by
      refine ⟨hsource, ?_, ?_, ?_, ?_, ?_⟩
      · intro hz x hx
        exact (hfuture 0 zero0 hz x).trans (hmap 0 zero0 (zeroG k) x hx)
      · intro hc x hx
        exact (hpsi hx).trans (hfuture c bottom0 hc x).symm
      · intro s hs0 hsE hsG x hx
        exact (hfuture s hs0 hsE x).trans (hmap s hs0 hsG x hx)
      · intro s hs0 hsE hsG x hx v w
        exact (hfutureMetric s hs0 hsE x v w).trans (hinner s hs0 hsG x hx v w)
      · intro hc x hx
        rw [hfuture c bottom0 hc x]
        exact hscalar x hx
    refine ⟨b, hb, E, hretain, hbound, ?_, ?_, ?_⟩
    · intro x hx v
      rw [hfutureMetric 0 zero0 _ x v v]
      exact hzeroInner x hx v
    · rw [hfuture 0 zero0 _ G.limit.base]
      exact hpoint
    · exact hstop.elim Or.inl (fun hcap => Or.inr hcap.2)
  let D := 2 * Real.sqrt (2 * Real.exp (6 * Bplus * window)) * R
  have hD : 0 < D := by dsimp only [D]; positivity
  have hscalarBad (k : ℕ) : ((F (n k)).connection (baseTime (n k))).scalarCurvature
      ((history (n k)).history.forward (baseTime (n k)) (hbaseTime (n k)) (basePoint (n k))) =
        (V).scale (n k) := (history (n k)).scalar_pullback _ _ _
  have hlong := limitFinite_uniform_cap_exclusion (C := G.limit.sliceCarrier)
    n baseTime (V).scale g G.limit.base R P
    hQ hR hcneg hd hwindow hbuffer hBplus (D := D) rfl hD (fun k => hPinched (n k))
    (fun k => (history (n k)).history.forward
      (baseTime (n k)) (hbaseTime (n k)) (basePoint (n k)))
    (fun k => hbad (n k)) hscalarBad Retain hsearch (by
      intro j
      filter_upwards [capBudget j] with k hk
      intro a ha E hscalar hEvent inst i contact hcontact hcap hdist y hy hnorm
      exact hk G.limit.sliceCarrier hU ha E hscalar hEvent i contact hcontact hcap
        hdist y hy hnorm)
  intro err herr
  filter_upwards [hlong err herr] with k hk
  obtain ⟨b, hb, E, hretain, hbound, hzeroInner, hpoint, hlong⟩ := hk
  obtain ⟨hsource, hzero, hpsi, hmap, hinner, hscalar⟩ := hretain
  have hb' : b ∈ Icc (-(H.toReal + 4 * d)) c :=
    ⟨by linarith only [hb.1], hb.2⟩
  exact ⟨b, hb', E, hsource, hzero, hpsi, hmap, hinner, hscalar,
    hbound, hzeroInner, hpoint, by linarith only [hlong]⟩

end PoincareConjecture.M47
