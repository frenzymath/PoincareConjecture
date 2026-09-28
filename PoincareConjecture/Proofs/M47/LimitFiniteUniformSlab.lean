import PoincareConjecture.Proofs.M47.LimitFiniteUniformApplication
import PoincareConjecture.Proofs.M47.LimitFiniteLongerSlab

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

private local instance uniformSlabTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance uniformSlabCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance uniformSlabManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
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

theorem limitFinite_exists_selected_longer_slab
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
    ∃ T : ℝ, 0 < T ∧ H.toReal < T ∧
      ∃ rho : ℕ → ℕ, ∃ hrho : StrictMono rho,
        rho = G.subsequence ∘ sigma ∘ etaIndex ∧
        TerminalCommonIntervalSlab (terminalCommonInterval_reindex V rho hrho) T := by
  obtain ⟨d, Bold, hd, _hdH, _hshort, hBold, sources⟩ :=
    limitFinite_eventually_uniform_endpoint_extension F W history baseTime hbaseTime
      basePoint hPositive hDiverges G sigma etaIndex P S B controls hfinite hsigma hetaIndex
      p O hInitial hConstants hC hBase hPinched rNext hThreshold hEarlier hOverlap hbad
      psi L hL hballs capBudget
  let T := H.toReal + d
  have hT : 0 < T := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hd
  have hHT : H.toReal < T := lt_add_of_pos_right _ hd
  let q := sigma ∘ etaIndex
  have hq : StrictMono q := hsigma.comp hetaIndex
  let rho := G.subsequence ∘ q
  have hrho : StrictMono rho := G.subsequence_strictMono.comp hq
  refine ⟨T, hT, hHT, rho, hrho, rfl, ?_⟩
  apply limitFinite_slab_of_preserved_sources F W history baseTime hbaseTime basePoint
    hPositive hDiverges G hfinite q hq hT
    (hBold.trans (le_max_right (13 * max (4 * L) 1) Bold))
  intro R hR err herr
  filter_upwards [sources R hR err herr] with k hk
  obtain ⟨b, _hb, E, hsource, _hzero, _hpsi, hmap, _hinner, _hscalar,
    hbound, _hquadratic, _hpoint, hlong⟩ := hk
  refine ⟨hsource, b, ?_, E, ?_, ?_, ?_⟩
  · change b < -(H.toReal + d)
    linarith only [hlong, hd]
  · intro s hs0 hsG hsE x hx
    exact hmap s hs0 hsE hsG x hx
  · intro s hs x hx
    exact (hbound s hs x hx).1
  · intro s hs x hx
    exact (hbound s hs x hx).2

end PoincareConjecture.M47
