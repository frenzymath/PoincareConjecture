import PoincareConjecture.Proofs.M47.LimitFiniteCapExclusion
import PoincareConjecture.Proofs.M47.LimitFiniteActualCandidates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

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

private local instance endpointRowsTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance endpointRowsCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance endpointRowsManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

local notation "U" => (fun j : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j))

variable
  (hbad : ∀ k, ¬ SurgeryCanonicalControl (F k) (baseTime k)
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))
    (F k).parameters.epsilon (F k).parameters.C)
  (capBudget :
    let seq := regularHistoryBlowupSequence F W history baseTime hbaseTime
      basePoint hPositive hDiverges
    ∀ j : ℕ, ∀ᶠ k in atTop,
    ∀ (C : GeneralizedSliceCarrier.{u}) {Ucap : Set C.carrier}, IsOpen Ucap →
    ∀ {a : ℝ} (ha : a ∈ Ico (-((j : ℝ) + 1)) 0),
    ∀ E : SurgeryFlowCylinder (F (G.subsequence k)) C (baseTime (G.subsequence k))
        (seq.scale (G.subsequence k)) (Icc a 0) Ucap,
      (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ Ucap,
        ((F (G.subsequence k)).connection
          (baseTime (G.subsequence k) + s / seq.scale (G.subsequence k))).scalarCurvature
            (E.forward s hs x) ≤ ((j : ℝ) + 1) * seq.scale (G.subsequence k)) →
      let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
      let zero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.2.le, le_rfl⟩
      let tbirth := baseTime (G.subsequence k) + a / seq.scale (G.subsequence k)
      ∀ (hEvent : tbirth ∈ (F (G.subsequence k)).surgery_times),
      ∀ [Nonempty ((F (G.subsequence k)).slice tbirth).carrier],
      ∀ (i : Fin ((F (G.subsequence k)).event tbirth hEvent).cap_count) (contact : C.carrier),
        contact ∈ Ucap →
        E.forward a bottom contact ∈
          (((F (G.subsequence k)).event tbirth hEvent).caps i).carrier →
        (∀ x ∈ Ucap, ((F (G.subsequence k)).metric tbirth).edist
          (E.forward a bottom contact) (E.forward a bottom x) ≤
            ENNReal.ofReal (((j : ℝ) + 1) / Real.sqrt (seq.scale (G.subsequence k)))) →
        ∀ y ∈ Ucap,
          ((F (G.subsequence k)).connection
            (baseTime (G.subsequence k) + 0 / seq.scale (G.subsequence k))).scalarCurvature
              (E.forward 0 zero y) = seq.scale (G.subsequence k) →
          SurgeryCanonicalControl (F (G.subsequence k))
            (baseTime (G.subsequence k) + 0 / seq.scale (G.subsequence k))
            (E.forward 0 zero y) (F (G.subsequence k)).parameters.epsilon
            (F (G.subsequence k)).parameters.C)

include hbad capBudget in

theorem limitFinite_actual_endpoint_rows
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
      (F k).parameters.delta t ≤ B.delta S.setup.standard_initial S.constants) :
    ∃ d K : ℕ → ℝ, (∀ j, 0 < d j) ∧ (∀ j, 0 < K j) ∧
      (∀ j, -H.toReal + d j / 4 ∈ blowupBackwardInterval H) ∧
      ∃ A : ∀ j, ℕ → RicciFlow 3 (U j) (Icc (-(H.toReal + d j / 2)) 0),
        ∀ j, ∀ᶠ k : ℕ in atTop,
          ∃ hI : Icc (-H.toReal + d j / 4) 0 ⊆ Icc (-G.exhaustion.time k) 0,
            G.exhaustion.space j ⊆ G.exhaustion.space k ∧
            ∃ (b : ℝ) (hb : b < -(H.toReal + d j / 2)),
              ∃ e : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
                  (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
                  (Icc b 0) (G.exhaustion.space j),
                (∀ s (hs : s ∈ Icc (-H.toReal + d j / 4) 0) (hs' : s ∈ Icc b 0),
                  ∀ x ∈ G.exhaustion.space j,
                    e.forward s hs' x = (history (G.subsequence k)).history.forward
                      (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))
                      (limitNoncollapse_physical_time_mem G k s (hI hs))
                      ((G.embedding k).forward s (hI hs) x)) ∧
                (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ G.exhaustion.space j,
                  |((F (G.subsequence k)).connection (baseTime (G.subsequence k) +
                    s / (V).scale (G.subsequence k))).curvatureTensorNorm (e.forward s hs x)| ≤
                      K j * (V).scale (G.subsequence k)) ∧
                (∀ s ∈ Icc (-(H.toReal + d j / 2)) 0, ∀ x : U j,
                  |((A j k).connection s).curvatureTensorNorm x| ≤ K j) ∧
                (∀ s (hs : s ∈ Icc (-(H.toReal + d j / 2)) 0) (x : U j),
                  ∀ v w : TangentSpace (𝓡 3) x,
                    ((A j k).metric s).inner x v w = e.pullbackInner s
                      ⟨hb.le.trans hs.1, hs.2⟩ x.val
                      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) x v)
                      (mfderiv (𝓡 3) (𝓡 3)
                        (Subtype.val : U j → G.limit.sliceCarrier.carrier) x w)) ∧
                ∀ s (_hs : s ∈ Icc (-(H.toReal + d j / 2)) 0)
                  (hs' : s ∈ Icc (-G.exhaustion.time k) 0) (x : U j),
                  ∀ v w : TangentSpace (𝓡 3) x,
                    ((A j k).metric s).inner x v w =
                      (G.embedding k).pullbackInner s hs' x.val
                        (mfderiv (𝓡 3) (𝓡 3)
                          (Subtype.val : U j → G.limit.sliceCarrier.carrier) x v)
                        (mfderiv (𝓡 3) (𝓡 3)
                          (Subtype.val : U j → G.limit.sliceCarrier.carrier) x w) := by
  classical
  obtain ⟨B0, _hB0, hnorm0⟩ := G.limit.curvature_locally_bounded_in_time {0}
    isCompact_singleton (singleton_subset_iff.mpr G.limit.zero_mem)
  have hterminal : ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection 0).curvatureTensorNorm x ≤ B0 :=
    fun x => (le_abs_self _).trans (hnorm0 0 (mem_singleton 0) x)
  choose d L D hd _hdsmall _hL _hD hc _hcneg search using fun m =>
    limitFinite_eventually_preserved_exhaustion_endpoint_without_cap F W history baseTime
      hbaseTime basePoint hPositive hDiverges G hbad capBudget P S B p O hH hfinite
      hInitial hConstants hParameters hBase hPinched rNext hThreshold hEarlier hOverlap
      hterminal m
  let K := fun m => 13 * max (4 * L m) 1
  have hK : ∀ m, 0 < K m := fun m => mul_pos (by norm_num)
    (lt_of_lt_of_le (by norm_num) (le_max_right (4 * L m) 1))
  have hlong (m : ℕ) : ∀ᶠ k : ℕ in atTop,
      ∃ hI : Icc (-H.toReal + d m / 4) 0 ⊆ Icc (-G.exhaustion.time k) 0,
        G.exhaustion.space m ⊆ G.exhaustion.space k ∧
        ∃ (b : ℝ) (_hb : b < -(H.toReal + d m / 2)),
          ∃ e : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
              (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
              (Icc b 0) (G.exhaustion.space m),
            (∀ s (hs : s ∈ Icc (-H.toReal + d m / 4) 0) (hs' : s ∈ Icc b 0),
              ∀ x ∈ G.exhaustion.space m,
                e.forward s hs' x = (history (G.subsequence k)).history.forward
                  (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))
                  (limitNoncollapse_physical_time_mem G k s (hI hs))
                  ((G.embedding k).forward s (hI hs) x)) ∧
            ∀ s (hs : s ∈ Icc b 0), ∀ x ∈ G.exhaustion.space m,
              |((F (G.subsequence k)).connection
                (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).curvatureTensorNorm
                  (e.forward s hs x)| ≤ K m * (V).scale (G.subsequence k) := by
    filter_upwards [search m 1 zero_lt_one] with k hk
    obtain ⟨hI, hspace, b, _hb, e, hmap, _hmetric, hbounds, _hdistance, hstrict⟩ := hk
    exact ⟨hI, hspace, b, hstrict, e, hmap,
      fun s hs x hx => (hbounds s hs x hx).2.1⟩
  choose A hactual using fun m => limitFinite_actual_source_candidates F W history baseTime
    hbaseTime basePoint hPositive hDiverges G P m (hd m) (hc m) (hlong m)
  exact ⟨d, K, hd, hK, hc, A, hactual⟩

end PoincareConjecture.M47
