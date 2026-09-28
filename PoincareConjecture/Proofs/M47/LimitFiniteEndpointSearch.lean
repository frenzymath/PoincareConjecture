import PoincareConjecture.Proofs.M47.LimitFiniteAnchorBounds
import PoincareConjecture.Proofs.M47.LimitFiniteCompactBounds
import PoincareConjecture.Proofs.M47.LimitNoncollapseShiftedSearchExistence
import PoincareConjecture.Proofs.M47.SeedVolume

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

private local instance endpointSearchTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance endpointSearchCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance endpointSearchManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem limitFinite_eventually_endpoint_search
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
    ∃ d L : ℝ, 0 < d ∧ 1 ≤ L ∧
      let shift := -H.toReal + d / 4
      shift ∈ blowupBackwardInterval H ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
        limitFiniteSliceTime G shift k = shift ∧
        G.exhaustion.space j ⊆ G.exhaustion.space k ∧
        let origin := limitFinitePhysicalSliceTime G shift k
        let U := limitFinitePhysicalSliceChart G F (fun i => (history i).history) shift k ''
          G.exhaustion.space j
        ∃ (a : ℝ) (ha : a ∈ Icc (-2 * d) 0),
          ∃ e : SurgeryFlowCylinder (F (G.subsequence k))
            ((F (G.subsequence k)).slice origin) origin ((V).scale (G.subsequence k))
            (Icc a 0) U,
            (∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x) ∧
            (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
              ((F (G.subsequence k)).connection
                (origin + s / (V).scale (G.subsequence k))).scalarCurvature
                  (e.forward s hs x) ≤ 4 * L * (V).scale (G.subsequence k) ∧
              |((F (G.subsequence k)).connection
                (origin + s / (V).scale (G.subsequence k))).curvatureTensorNorm
                  (e.forward s hs x)| ≤
                (13 * max (4 * L) 1) * (V).scale (G.subsequence k) ∧
              ((F (G.subsequence k)).connection
                (origin + s / (V).scale (G.subsequence k))).negativeCurvaturePart
                  (e.forward s hs x) ≤ eta * (V).scale (G.subsequence k)) ∧
            (shift + a < -H.toReal - d / 2 ∨ a ∈ Icc (-d) 0 ∧
              ∃ hEvent : origin + a / (V).scale (G.subsequence k) ∈
                  (F (G.subsequence k)).surgery_times,
                ∀ [Nonempty ((F (G.subsequence k)).slice
                    (origin + a / (V).scale (G.subsequence k))).carrier],
                  ∃ i : Fin ((F (G.subsequence k)).event
                    (origin + a / (V).scale (G.subsequence k)) hEvent).cap_count,
                    Set.Nonempty (e.forward a ⟨le_rfl, ha.2⟩ '' U ∩
                      (((F (G.subsequence k)).event
                        (origin + a / (V).scale (G.subsequence k)) hEvent).caps i).carrier)) := by
  have hT : 0 < H.toReal := ENNReal.toReal_pos hH.ne' hfinite
  have heps := S.setup.epsilon_pos
  have heps₀ : S.setup.epsilon ≤ S.calibration.epsilon₁₀ := by
    linarith [S.calibration.two_epsilon_le_bounded_distance]
  have hsmall : 2 * S.setup.epsilon < 1 / 2 :=
    lt_of_le_of_lt
      (S.calibration.two_epsilon_le_bounded_distance.trans S.calibration.epsilon₁₀_le)
      (by norm_num)
  obtain ⟨K, hK, hbound⟩ := limitFinite_compact_curvature_bound F W history baseTime
    hbaseTime basePoint hPositive hDiverges G P S hH hfinite heps hsmall
    (heps₀.trans S.calibration.epsilon₁₀_le) heps₀ S.setup.C_pos hParameters
    (fun k t ht => hPinched k t ((W k).time_subset ht)) rNext hThreshold hEarlier
    hterminal (G.exhaustion.space_compactClosure j)
  let L : ℝ := 3 * (9 * K + 1)
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  let A := blowupAnalyticConstant S B
  have hA : 0 < A := blowupAnalyticConstant_pos S B
  let d := min (H.toReal / 2) (min (1 / 4) (1 / (128 * A * L)))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdT : d ≤ H.toReal / 2 := min_le_left _ _
  have hdsmall : d ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdtime : d ≤ 1 / (128 * A * L) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hshort : 64 * blowupAnalyticConstant S B * L * (2 * d) ≤ 1 := by
    have hprod : 0 < 128 * A * L := by positivity
    have h := (le_div_iff₀ hprod).mp hdtime
    change 64 * A * L * (2 * d) ≤ 1
    nlinarith only [h]
  let shift := -H.toReal + d / 4
  have hshift : shift ∈ blowupBackwardInterval H := by
    rw [limitFinite_domain_eq hfinite]
    dsimp only [shift]
    constructor <;> linarith
  have hshift0 : shift ≤ 0 := by dsimp only [shift]; linarith
  have hbuffer : -(H.toReal + 1) ≤ shift - 2 * d := by
    dsimp only [shift]
    linarith
  refine ⟨d, L, hd, hL, hshift, ?_⟩
  intro eta heta
  have hanchor := limitFinite_eventually_physical_anchor_bounds F W history baseTime
    hbaseTime basePoint hPositive hDiverges G P shift hshift
    (G.exhaustion.space_compactClosure j)
    (fun x hx => lt_of_le_of_lt (hbound shift hshift x hx).2
      (by linarith : 9 * K < 9 * K + 1))
  have hQ := (V).scalar_diverges.comp G.subsequence_strictMono.tendsto_atTop
  filter_upwards [hanchor,
    hQ.eventually (eventually_ge_atTop (64 * ((H.toReal + 1) + 1))),
    hQ.eventually (eventually_ge_atTop B.curvature_threshold),
    hQ.eventually (eventually_ge_atTop (blowupPinchingThreshold (4 * L) eta))]
    with k hk hscale hlarge hpinching
  let phi := limitFinitePhysicalSliceChart G F (fun i => (history i).history) shift k
  let U := phi '' G.exhaustion.space j
  have hsource : G.exhaustion.space j ⊆ phi.source := by
    rw [limitFinite_physical_slice_chart_source]
    exact subset_closure.trans hk.2.1
  have hU : IsOpen U := phi.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (G.exhaustion.space_open j) hsource
  have hne : U.Nonempty := ⟨phi G.limit.base, mem_image_of_mem phi (G.exhaustion.base_mem j)⟩
  have hscalar : ∀ x ∈ U,
      ((F (G.subsequence k)).connection
        (limitFinitePhysicalSliceTime G shift k)).scalarCurvature x ≤
          L * (V).scale (G.subsequence k) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hk.2.2 x (subset_closure hx)).2.le
  have hpast : SurgeryCanonicalOn (F (G.subsequence k))
      (surgeryObservationInterval (O (G.subsequence k)) ∩ Iio (baseTime (G.subsequence k)))
      (rNext (G.subsequence k)) := by
    intro t ht
    exact hEarlier (G.subsequence k) t ⟨ht.1.1, ht.2⟩
  obtain ⟨a, ha, e, hbased, hbounds, hstop⟩ := limitFinite_exists_shifted_bounded_search
    S B (p (G.subsequence k)) (O (G.subsequence k)) (hInitial (G.subsequence k))
    (hConstants (G.subsequence k)) (hParameters (G.subsequence k)).2
    (hBase (G.subsequence k)) (by linarith : 0 ≤ H.toReal + 1) hscale hlarge
    (hThreshold (G.subsequence k)) (hPinched (G.subsequence k)) hpast
    (hOverlap (G.subsequence k)) P.toM46
    (show limitFiniteSliceTime G shift k ≤ 0 by rwa [hk.1]) hd
    (show -(H.toReal + 1) ≤ limitFiniteSliceTime G shift k - 2 * d by rwa [hk.1])
    hL hshort U hU hne hscalar heta hpinching
  refine ⟨hk.1, subset_closure.trans hk.2.1, a, ha, e, hbased, hbounds, ?_⟩
  rcases hstop with hlong | hcap
  · exact Or.inl (by linarith)
  · exact Or.inr hcap

end PoincareConjecture.M47
