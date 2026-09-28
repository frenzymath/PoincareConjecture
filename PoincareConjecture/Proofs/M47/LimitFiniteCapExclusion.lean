import PoincareConjecture.Proofs.M47.TerminalRegularFiniteCapBudget
import PoincareConjecture.Proofs.M47.LimitFiniteBallEndpoint
import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalChart
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction

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

private local instance finiteCapTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance finiteCapCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteCapManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

variable
  (hbad : ∀ k, ¬ SurgeryCanonicalControl (F k) (baseTime k)
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))
    (F k).parameters.epsilon (F k).parameters.C)
  (capBudget :
    let seq := regularHistoryBlowupSequence F W history baseTime hbaseTime
      basePoint hPositive hDiverges
    ∀ j : ℕ, ∀ᶠ k in atTop,
    ∀ (C : GeneralizedSliceCarrier.{u}) {U : Set C.carrier}, IsOpen U →
    ∀ {a : ℝ} (ha : a ∈ Ico (-((j : ℝ) + 1)) 0),
    ∀ E : SurgeryFlowCylinder (F (G.subsequence k)) C (baseTime (G.subsequence k))
        (seq.scale (G.subsequence k)) (Icc a 0) U,
      (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
        ((F (G.subsequence k)).connection
          (baseTime (G.subsequence k) + s / seq.scale (G.subsequence k))).scalarCurvature
            (E.forward s hs x) ≤ ((j : ℝ) + 1) * seq.scale (G.subsequence k)) →
      let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
      let zero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.2.le, le_rfl⟩
      let tbirth := baseTime (G.subsequence k) + a / seq.scale (G.subsequence k)
      ∀ (hEvent : tbirth ∈ (F (G.subsequence k)).surgery_times),
      ∀ [Nonempty ((F (G.subsequence k)).slice tbirth).carrier],
      ∀ (i : Fin ((F (G.subsequence k)).event tbirth hEvent).cap_count) (contact : C.carrier),
        contact ∈ U →
        E.forward a bottom contact ∈
          (((F (G.subsequence k)).event tbirth hEvent).caps i).carrier →
        (∀ x ∈ U, ((F (G.subsequence k)).metric tbirth).edist
          (E.forward a bottom contact) (E.forward a bottom x) ≤
            ENNReal.ofReal (((j : ℝ) + 1) / Real.sqrt (seq.scale (G.subsequence k)))) →
        ∀ y ∈ U,
          ((F (G.subsequence k)).connection
            (baseTime (G.subsequence k) + 0 / seq.scale (G.subsequence k))).scalarCurvature
              (E.forward 0 zero y) = seq.scale (G.subsequence k) →
          SurgeryCanonicalControl (F (G.subsequence k))
            (baseTime (G.subsequence k) + 0 / seq.scale (G.subsequence k))
            (E.forward 0 zero y) (F (G.subsequence k)).parameters.epsilon
            (F (G.subsequence k)).parameters.C)

include hbad capBudget in

theorem limitFinite_eventually_preserved_ball_endpoint_without_cap
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : ℕ → SurgeryParameterPrefix S.constants) (O : ∀ k, SurgeryObservation (F k))
    (hH : 0 < H) (hfinite : H ≠ ⊤)
    (hInitial : ∀ k, (F k).standard_initial = S.setup.standard_initial)
    (hConstants : ∀ k, (F k).local_constants = S.constants)
    (hParameters : ∀ k, (F k).parameters.epsilon = S.setup.epsilon ∧
      (F k).parameters.C = S.setup.C)
    (hBase : ∀ k, baseTime k ∈ Ico (surgeryEpochStart (p k).i) (O k).H)
    (hPinched : ∀ k, SurgeryFlowPinched (F k))
    (rNext : ℕ → ℝ) (hThreshold : ∀ k, (rNext k)⁻¹ ^ 2 ≤ (V).scale k)
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (rNext k))
    (hOverlap : ∀ k, ∀ t ∈ surgeryObservationInterval (O k) ∩
        Ico (surgeryEpochStart ((p k).i - 1)) (O k).H,
      (F k).parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)
    {B0 : ℝ} (hterminal : ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection 0).curvatureTensorNorm x ≤ B0)
    (R : ℝ) (hR : 0 < R) :
    let U := (G.limit.flow.metric 0).ball G.limit.base R
    ∃ d L D : ℝ, 0 < d ∧ d ≤ 1 / 4 ∧ 1 ≤ L ∧ 0 < D ∧
      let c := -H.toReal + d / 4
      ∃ hc : c ∈ blowupBackwardInterval H, c < 0 ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
        ∃ hI : Icc c 0 ⊆ Icc (-G.exhaustion.time k) 0,
          U ⊆ G.exhaustion.space k ∧
          ∃ (b : ℝ) (hb : b ∈ Icc (c - 2 * d) c),
            ∃ E : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
                (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
                (Icc b 0) U,
              (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0),
                ∀ x ∈ U,
                  E.forward s hs' x = (history (G.subsequence k)).history.forward
                    (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))
                    (limitNoncollapse_physical_time_mem G k s (hI hs))
                    ((G.embedding k).forward s (hI hs) x)) ∧
              (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0),
                ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
                  E.pullbackInner s hs' x v w =
                    (G.embedding k).pullbackInner s (hI hs) x v w) ∧
              (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U,
                ((F (G.subsequence k)).connection
                  (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).scalarCurvature
                    (E.forward s hs x) ≤ 4 * L * (V).scale (G.subsequence k) ∧
                |((F (G.subsequence k)).connection
                  (baseTime (G.subsequence k) +
                    s / (V).scale (G.subsequence k))).curvatureTensorNorm
                    (E.forward s hs x)| ≤ (13 * max (4 * L) 1) * (V).scale (G.subsequence k) ∧
                ((F (G.subsequence k)).connection
                  (baseTime (G.subsequence k) +
                    s / (V).scale (G.subsequence k))).negativeCurvaturePart
                    (E.forward s hs x) ≤ eta * (V).scale (G.subsequence k)) ∧
              (∀ contact ∈ U, ∀ x ∈ U,
                ((F (G.subsequence k)).metric
                  (baseTime (G.subsequence k) + b / (V).scale (G.subsequence k))).edist
                  (E.forward b ⟨le_rfl, hb.2.trans hc.1⟩ contact)
                  (E.forward b ⟨le_rfl, hb.2.trans hc.1⟩ x) ≤
                    ENNReal.ofReal (D / Real.sqrt ((V).scale (G.subsequence k)))) ∧
              b < -(H.toReal + d / 2) := by
  intro U
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  have hU : IsOpen U := M04.initial_ball_isOpen (G.limit.flow.metric 0) G.limit.base R
  have hbaseU : G.limit.base ∈ U := by
    change (G.limit.flow.metric 0).edist G.limit.base G.limit.base < ENNReal.ofReal R
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hR
  obtain ⟨d, L, D, hd, hdsmall, hL, hD, hc, hcneg, search⟩ :=
    limitFinite_eventually_preserved_ball_endpoint_search F W history baseTime hbaseTime
      basePoint hPositive hDiverges G P S B p O hH hfinite hInitial hConstants hParameters
      hBase hPinched rNext hThreshold hEarlier hOverlap hterminal R hR
  let c := -H.toReal + d / 4
  obtain ⟨j, hj⟩ := exists_nat_ge (max (H.toReal + 1) (max (4 * L) D))
  have hTj : H.toReal + 1 ≤ (j : ℝ) + 1 :=
    ((le_max_left _ _).trans hj).trans (le_add_of_nonneg_right zero_le_one)
  have hLj : 4 * L ≤ (j : ℝ) + 1 :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hj).trans
      (le_add_of_nonneg_right zero_le_one)
  have hDj : D ≤ (j : ℝ) + 1 :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hj).trans
      (le_add_of_nonneg_right zero_le_one)
  refine ⟨d, L, D, hd, hdsmall, hL, hD, hc, hcneg, ?_⟩
  intro eta heta
  filter_upwards [search eta heta, capBudget j] with k hk hcapControl
  obtain ⟨hI, hspace, b, hb, E, hmap, hmetric, hbounds, hdistance, hstop⟩ := hk
  refine ⟨hI, hspace, b, hb, E, hmap, hmetric, hbounds, hdistance, ?_⟩
  rcases hstop with hlong | ⟨_hbcap, hEvent, hcap⟩
  · linarith only [hlong]
  exfalso
  have hQ : 0 < (V).scale (G.subsequence k) := E.scale_pos
  have ha : b ∈ Ico (-((j : ℝ) + 1)) 0 := by
    refine ⟨?_, hb.2.trans_lt hcneg⟩
    have hlo : -H.toReal + d / 4 - 2 * d ≤ b := hb.1
    linarith only [hlo, hdsmall, hTj]
  let bottom : b ∈ Icc b 0 := ⟨le_rfl, ha.2.le⟩
  let zero : (0 : ℝ) ∈ Icc b 0 := ⟨ha.2.le, le_rfl⟩
  let oldZero : (0 : ℝ) ∈ Icc c 0 := ⟨hcneg.le, le_rfl⟩
  let : Nonempty ((F (G.subsequence k)).slice
      (baseTime (G.subsequence k) + b / (V).scale (G.subsequence k))).carrier :=
    ⟨E.forward b bottom G.limit.base⟩
  obtain ⟨i, z, hzimage, hzcap⟩ := hcap
  obtain ⟨contact, hcontact, rfl⟩ := hzimage
  have hpoint : (⟨baseTime (G.subsequence k) + 0 / (V).scale (G.subsequence k),
      E.forward 0 zero G.limit.base⟩ : Σ t, ((F (G.subsequence k)).slice t).carrier) =
      ⟨baseTime (G.subsequence k), (history (G.subsequence k)).history.forward
        (baseTime (G.subsequence k)) (hbaseTime (G.subsequence k))
        (basePoint (G.subsequence k))⟩ := by
    have hp := limitCanonicalPhysicalChart_point_identity (G.embedding k)
      (G.exhaustion.space_open k) (history (G.subsequence k)).history
      0 (hI oldZero) (limitNoncollapse_physical_time_mem G k 0 (hI oldZero))
      G.limit.base ((V).base (G.subsequence k)) (hbaseTime (G.subsequence k))
      (G.base_preserving k (hI oldZero))
    change (⟨baseTime (G.subsequence k) + 0 / (V).scale (G.subsequence k),
      (history (G.subsequence k)).history.forward
        (baseTime (G.subsequence k) + 0 / (V).scale (G.subsequence k))
        (limitNoncollapse_physical_time_mem G k 0 (hI oldZero))
        ((G.embedding k).forward 0 (hI oldZero) G.limit.base)⟩ :
      Σ t, ((F (G.subsequence k)).slice t).carrier) = _ at hp
    rw [← hmap 0 oldZero zero G.limit.base hbaseU] at hp
    exact hp
  have hscalar : ((F (G.subsequence k)).connection
      (baseTime (G.subsequence k) + 0 / (V).scale (G.subsequence k))).scalarCurvature
        (E.forward 0 zero G.limit.base) = (V).scale (G.subsequence k) :=
    (congrArg (fun w : Σ t, ((F (G.subsequence k)).slice t).carrier =>
      ((F (G.subsequence k)).connection w.1).scalarCurvature w.2) hpoint).trans
        ((history (G.subsequence k)).scalar_pullback
          (baseTime (G.subsequence k)) (hbaseTime (G.subsequence k))
          (basePoint (G.subsequence k)))
  have hcontrol := hcapControl G.limit.sliceCarrier hU ha E
    (fun s hs x hx => (hbounds s hs x hx).1.trans
      (mul_le_mul_of_nonneg_right hLj hQ.le)) hEvent i contact hcontact hzcap
    (fun x hx => (hdistance contact hcontact x hx).trans
      (ENNReal.ofReal_mono (div_le_div_of_nonneg_right hDj (Real.sqrt_nonneg _))))
    G.limit.base hbaseU hscalar
  have hbadControl := (congrArg
    (fun w : Σ t, ((F (G.subsequence k)).slice t).carrier =>
      SurgeryCanonicalControl (F (G.subsequence k)) w.1 w.2
        (F (G.subsequence k)).parameters.epsilon (F (G.subsequence k)).parameters.C)
    hpoint).mp hcontrol
  exact hbad (G.subsequence k) hbadControl

include hbad capBudget in

theorem limitFinite_eventually_preserved_exhaustion_endpoint_without_cap
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : ℕ → SurgeryParameterPrefix S.constants) (O : ∀ k, SurgeryObservation (F k))
    (hH : 0 < H) (hfinite : H ≠ ⊤)
    (hInitial : ∀ k, (F k).standard_initial = S.setup.standard_initial)
    (hConstants : ∀ k, (F k).local_constants = S.constants)
    (hParameters : ∀ k, (F k).parameters.epsilon = S.setup.epsilon ∧
      (F k).parameters.C = S.setup.C)
    (hBase : ∀ k, baseTime k ∈ Ico (surgeryEpochStart (p k).i) (O k).H)
    (hPinched : ∀ k, SurgeryFlowPinched (F k))
    (rNext : ℕ → ℝ) (hThreshold : ∀ k, (rNext k)⁻¹ ^ 2 ≤ (V).scale k)
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (rNext k))
    (hOverlap : ∀ k, ∀ t ∈ surgeryObservationInterval (O k) ∩
        Ico (surgeryEpochStart ((p k).i - 1)) (O k).H,
      (F k).parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)
    {B0 : ℝ} (hterminal : ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection 0).curvatureTensorNorm x ≤ B0)
    (j : ℕ) :
    ∃ d L D : ℝ, 0 < d ∧ d ≤ 1 / 4 ∧ 1 ≤ L ∧ 0 < D ∧
      let c := -H.toReal + d / 4
      ∃ hc : c ∈ blowupBackwardInterval H, c < 0 ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
        ∃ hI : Icc c 0 ⊆ Icc (-G.exhaustion.time k) 0,
          G.exhaustion.space j ⊆ G.exhaustion.space k ∧
          ∃ (b : ℝ) (hb : b ∈ Icc (c - 2 * d) c),
            ∃ E : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
                (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
                (Icc b 0) (G.exhaustion.space j),
              (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0),
                ∀ x ∈ G.exhaustion.space j,
                  E.forward s hs' x = (history (G.subsequence k)).history.forward
                    (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))
                    (limitNoncollapse_physical_time_mem G k s (hI hs))
                    ((G.embedding k).forward s (hI hs) x)) ∧
              (∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0),
                ∀ x ∈ G.exhaustion.space j, ∀ v w : TangentSpace (𝓡 3) x,
                  E.pullbackInner s hs' x v w =
                    (G.embedding k).pullbackInner s (hI hs) x v w) ∧
              (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ G.exhaustion.space j,
                ((F (G.subsequence k)).connection
                  (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).scalarCurvature
                    (E.forward s hs x) ≤ 4 * L * (V).scale (G.subsequence k) ∧
                |((F (G.subsequence k)).connection
                  (baseTime (G.subsequence k) +
                    s / (V).scale (G.subsequence k))).curvatureTensorNorm
                    (E.forward s hs x)| ≤ (13 * max (4 * L) 1) * (V).scale (G.subsequence k) ∧
                ((F (G.subsequence k)).connection
                  (baseTime (G.subsequence k) +
                    s / (V).scale (G.subsequence k))).negativeCurvaturePart
                    (E.forward s hs x) ≤ eta * (V).scale (G.subsequence k)) ∧
              (∀ contact ∈ G.exhaustion.space j, ∀ x ∈ G.exhaustion.space j,
                ((F (G.subsequence k)).metric
                  (baseTime (G.subsequence k) + b / (V).scale (G.subsequence k))).edist
                  (E.forward b ⟨le_rfl, hb.2.trans hc.1⟩ contact)
                  (E.forward b ⟨le_rfl, hb.2.trans hc.1⟩ x) ≤
                    ENNReal.ofReal (D / Real.sqrt ((V).scale (G.subsequence k)))) ∧
              b < -(H.toReal + d / 2) := by
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let g := G.limit.flow.metric 0
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace (G.limit.complete 0 G.limit.zero_mem)
  obtain ⟨R, hR, hcapture⟩ :=
    (G.exhaustion.space_compactClosure j).isBounded.subset_ball_lt 0 G.limit.base
  have hsource : G.exhaustion.space j ⊆ g.ball G.limit.base R := by
    intro x hx
    rw [← g.toMetricSpace_ball]
    exact hcapture (subset_closure hx)
  obtain ⟨d, L, D, hd, hdsmall, hL, hD, hc, hcneg, source⟩ :=
    limitFinite_eventually_preserved_ball_endpoint_without_cap F W history baseTime hbaseTime
      basePoint hPositive hDiverges G hbad capBudget P S B p O hH hfinite hInitial
      hConstants hParameters hBase hPinched rNext hThreshold hEarlier hOverlap hterminal R hR
  refine ⟨d, L, D, hd, hdsmall, hL, hD, hc, hcneg, ?_⟩
  intro eta heta
  filter_upwards [source eta heta] with k hk
  obtain ⟨hI, hspace, b, hb, E, hmap, hmetric, hbounds, hdistance, hlong⟩ := hk
  let restricted := E.restrict (Subset.refl _) ordConnected_Icc hsource
  refine ⟨hI, hsource.trans hspace, b, hb, restricted, ?_, ?_, ?_, ?_, hlong⟩
  · intro s hs hs' x hx
    exact hmap s hs hs' x (hsource hx)
  · intro s hs hs' x hx v w
    exact hmetric s hs hs' x (hsource hx) v w
  · intro s hs x hx
    exact hbounds s hs x (hsource hx)
  · intro contact hcontact x hx
    exact hdistance contact (hsource hcontact) x (hsource hx)

end PoincareConjecture.M47
