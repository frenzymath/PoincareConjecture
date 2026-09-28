import PoincareConjecture.Proofs.M47.LimitFinitePreservedEndpoint









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

private local instance openEndpointTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance openEndpointCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance openEndpointManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold



theorem limitFinite_eventually_preserved_open_endpoint_search
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
    (U : Set G.limit.carrier.carrier) (hU : IsOpen U)
    (hUcompact : IsCompact (closure U)) (hUne : U.Nonempty) :
    ∃ d L : ℝ, 0 < d ∧ d ≤ 1 / 4 ∧ 1 ≤ L ∧
      let c := -H.toReal + d / 4
      ∃ hc : c ∈ blowupBackwardInterval H, c < 0 ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
        ∃ hI : Icc c 0 ⊆ Icc (-G.exhaustion.time k) 0,
          U ⊆ G.exhaustion.space k ∧
          ∃ (b : ℝ) (hb : b ∈ Icc (c - 2 * d) c),
            ∃ E : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
                (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
                (Icc b 0) (U),
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
              (b < -H.toReal - d / 2 ∨ b ∈ Icc (c - d) c ∧
                ∃ hEvent : baseTime (G.subsequence k) + b / (V).scale (G.subsequence k) ∈
                    (F (G.subsequence k)).surgery_times,
                  ∀ [Nonempty ((F (G.subsequence k)).slice
                      (baseTime (G.subsequence k) + b / (V).scale (G.subsequence k))).carrier],
                    ∃ i : Fin ((F (G.subsequence k)).event
                      (baseTime (G.subsequence k) +
                        b / (V).scale (G.subsequence k)) hEvent).cap_count,
                      Set.Nonempty (E.forward b ⟨le_rfl, hb.2.trans (by
                        exact hc.1)⟩ ''
                          U ∩
                        (((F (G.subsequence k)).event
                          (baseTime (G.subsequence k) + b / (V).scale (G.subsequence k))
                            hEvent).caps i).carrier)) := by
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
    hterminal hUcompact
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
  let c := -H.toReal + d / 4
  have hc : c ∈ blowupBackwardInterval H := by
    rw [limitFinite_domain_eq hfinite]
    dsimp only [c]
    constructor <;> linarith
  have hc0 : c ≤ 0 := hc.1
  have hCJ : Icc c 0 ⊆ blowupBackwardInterval H := by
    intro s hs
    rw [limitFinite_domain_eq hfinite] at hc ⊢
    exact ⟨hc.1.trans_le hs.1, hs.2⟩
  have hbuffer : -(H.toReal + 1) ≤ c - 2 * d := by
    dsimp only [c]
    linarith
  have hcneg : c < 0 := by dsimp only [c]; linarith only [hT, hdT]
  refine ⟨d, L, hd, hdsmall, hL, hc, hcneg, ?_⟩
  intro eta heta
  have hsource := limitNoncollapse_generalized_compact_curvature_lt G P
    isCompact_Icc hCJ hUcompact
    (fun s hs x hx => lt_of_le_of_lt (hbound s (hCJ hs) x hx).2
      (by linarith : 9 * K < 9 * K + 1))
  have hQtail := (V).scalar_diverges.comp G.subsequence_strictMono.tendsto_atTop
  filter_upwards [hsource,
    hQtail.eventually (eventually_ge_atTop (64 * ((H.toReal + 1) + 1))),
    hQtail.eventually (eventually_ge_atTop B.curvature_threshold),
    hQtail.eventually (eventually_ge_atTop (blowupPinchingThreshold (4 * L) eta))]
    with k hk hscale hlarge hpinching
  have hspace : U ⊆ G.exhaustion.space k := subset_closure.trans hk.2.1
  let original := (G.embedding k).restrict hk.1 hspace
  obtain ⟨e0, hmap, hmetric⟩ :=
    (history (G.subsequence k)).cylinders_to_surgery G.limit.sliceCarrier
      (baseTime (G.subsequence k)) ((V).scale (G.subsequence k)) (Icc c 0)
      U ordConnected_Icc hU
      (fun s hs => limitNoncollapse_physical_time_mem G k s (hk.1 hs)) original
  have hQ := e0.scale_pos
  have hscalar (s : ℝ) (hs : s ∈ Icc c 0) (x : G.limit.carrier.carrier)
      (hx : x ∈ U) :
      ((F (G.subsequence k)).connection
        (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).scalarCurvature
          (e0.forward s hs x) ≤ L * (V).scale (G.subsequence k) := by
    have hnorm : ((F (G.subsequence k)).connection
        (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).curvatureTensorNorm
          (e0.forward s hs x) < (9 * K + 1) * (V).scale (G.subsequence k) := by
      rw [hmap s hs x hx, (history (G.subsequence k)).curvature_norm_pullback]
      exact (div_lt_iff₀ hQ).mp (hk.2.2 s hs (hk.1 hs) x (subset_closure hx))
    have hR := ((F (G.subsequence k)).connection
      (baseTime (G.subsequence k) +
        s / (V).scale (G.subsequence k))).scalarCurvature_le_curvatureTensorNorm_sharp
        (e0.forward s hs x)
    norm_num only [Nat.cast_ofNat] at hR
    dsimp only [L]
    nlinarith only [hR, hnorm]
  have hpast : SurgeryCanonicalOn (F (G.subsequence k))
      (surgeryObservationInterval (O (G.subsequence k)) ∩ Iio (baseTime (G.subsequence k)))
      (rNext (G.subsequence k)) := by
    intro t ht
    exact hEarlier (G.subsequence k) t ⟨ht.1.1, ht.2⟩
  have hsearch0 := limitFinite_exists_preserved_bounded_search S B (p (G.subsequence k))
    (O (G.subsequence k)) (hInitial (G.subsequence k)) (hConstants (G.subsequence k))
    (hParameters (G.subsequence k)).2 (hBase (G.subsequence k))
    (by linarith : 0 ≤ H.toReal + 1) hscale hlarge (hThreshold (G.subsequence k))
    (hPinched (G.subsequence k)) hpast (hOverlap (G.subsequence k)) P.toM46
    (Q := (V).scale (G.subsequence k)) (shift := 0) (c := c) (d := d) (L := L) (eta := eta)
    (C := G.limit.sliceCarrier) (U := U)
  rw [zero_div, add_zero, zero_add] at hsearch0
  obtain ⟨b, hb, E, hfuture, hnew, hstop⟩ := hsearch0 e0 le_rfl hc0 hd hbuffer hL hshort
    hU hUne
    (hscalar c ⟨le_rfl, hc0⟩) heta hpinching
  refine ⟨hk.1, hspace, b, hb, E, ?_, ?_, ?_, ?_⟩
  · intro s hs hs' x hx
    exact (hfuture s hs hs' x).trans (hmap s hs x hx)
  · intro s hs hs' x hx v w
    have heq : E.forward s hs' =ᶠ[𝓝 x] e0.forward s hs := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hfuture s hs hs' y
    unfold SurgeryFlowCylinder.pullbackInner
    rw [heq.self_of_nhds, heq.mfderiv_eq]
    exact hmetric s hs x hx v w
  · intro s hs x hx
    have hR : ((F (G.subsequence k)).connection
        (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).scalarCurvature
          (E.forward s hs x) ≤ 4 * L * (V).scale (G.subsequence k) := by
      by_cases hsc : s ≤ c
      · exact (hnew s ⟨hs.1, hsc⟩ x hx).1
      · have hcs : c ≤ s := (lt_of_not_ge hsc).le
        rw [hfuture s ⟨hcs, hs.2⟩ hs x]
        apply (hscalar s _ x hx).trans
        nlinarith only [hQ, hL]
    exact ⟨hR, pinched_blowup_curvature_bounds P.toM46
      (hPinched (G.subsequence k) _ (E.time_subset (mem_image_of_mem _ hs)))
      (by linarith : 0 ≤ 4 * L) heta hpinching (mem_univ _) hR⟩
  · rcases hstop with hlong | hcap
    · exact Or.inl (by dsimp only [c] at hlong; linarith)
    · exact Or.inr hcap

end PoincareConjecture.M47
