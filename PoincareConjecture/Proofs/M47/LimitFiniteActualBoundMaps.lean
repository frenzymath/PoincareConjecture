import PoincareConjecture.Proofs.M47.LimitFiniteActualMetric
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointPhysicalMaps










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "Euc" => EuclideanSpace ℝ (Fin 3)

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

variable {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
  (blowupBackwardInterval H))

private local instance actualMapsTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance actualMapsCharts : ChartedSpace Euc G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance actualMapsManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

local notation "U" => (fun j : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j))



theorem limitFinite_actual_endpoint_physical_maps
    (hfinite : H ≠ ⊤) (d K : ℕ → ℝ) (hd : ∀ j, 0 < d j)
    (hc : ∀ j, -H.toReal + d j / 4 ∈ blowupBackwardInterval H)
    (A : ∀ j, ℕ → RicciFlow 3 (U j) (Icc (-(H.toReal + d j / 2)) 0))
    (hactual :
      let seq := regularHistoryBlowupSequence F W history baseTime hbaseTime
        basePoint hPositive hDiverges
      ∀ j, ∀ᶠ k : ℕ in atTop,
        ∃ hI : Icc (-H.toReal + d j / 4) 0 ⊆ Icc (-G.exhaustion.time k) 0,
          G.exhaustion.space j ⊆ G.exhaustion.space k ∧
          ∃ (b : ℝ) (hb : b < -(H.toReal + d j / 2)),
            ∃ e : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
                (baseTime (G.subsequence k)) (seq.scale (G.subsequence k))
                (Icc b 0) (G.exhaustion.space j),
              (∀ s (hs : s ∈ Icc (-H.toReal + d j / 4) 0) (hs' : s ∈ Icc b 0),
                ∀ x ∈ G.exhaustion.space j,
                  e.forward s hs' x = (history (G.subsequence k)).history.forward
                    (baseTime (G.subsequence k) + s / seq.scale (G.subsequence k))
                    (limitNoncollapse_physical_time_mem G k s (hI hs))
                    ((G.embedding k).forward s (hI hs) x)) ∧
              (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ G.exhaustion.space j,
                |((F (G.subsequence k)).connection (baseTime (G.subsequence k) +
                  s / seq.scale (G.subsequence k))).curvatureTensorNorm (e.forward s hs x)| ≤
                    K j * seq.scale (G.subsequence k)) ∧
              (∀ s ∈ Icc (-(H.toReal + d j / 2)) 0, ∀ x : U j,
                |((A j k).connection s).curvatureTensorNorm x| ≤ K j) ∧
              (∀ s (hs : s ∈ Icc (-(H.toReal + d j / 2)) 0) (x : U j),
                ∀ v w : TangentSpace (𝓡 3) x,
                  ((A j k).metric s).inner x v w = e.pullbackInner s
                    ⟨hb.le.trans hs.1, hs.2⟩ x.val
                    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) x v)
                    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) x w)) ∧
              ∀ s (_hs : s ∈ Icc (-(H.toReal + d j / 2)) 0)
                (hs' : s ∈ Icc (-G.exhaustion.time k) 0) (x : U j),
                ∀ v w : TangentSpace (𝓡 3) x,
                  ((A j k).metric s).inner x v w = (G.embedding k).pullbackInner s hs' x.val
                    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) x v)
                    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) x w))
    (j : ℕ → ℕ) (hj : ∀ m, closure (G.exhaustion.space m) ⊆ G.exhaustion.space (j m))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    let seq := regularHistoryBlowupSequence F W history baseTime hbaseTime
      basePoint hPositive hDiverges
    ∃ η : ℕ → ℕ, StrictMono η ∧
      StrictMono (fun k => G.subsequence (σ (η k))) ∧
      ∃ ψ : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.sliceCarrier.carrier
          ((F (G.subsequence (σ (η k)))).slice
            (baseTime (G.subsequence (σ (η k))) +
              -H.toReal / seq.scale (G.subsequence (σ (η k))))).carrier ∞,
        (∀ k, (ψ k).source = G.exhaustion.space k) ∧
        (∀ k, 0 < seq.scale (G.subsequence (σ (η k))) ∧
          baseTime (G.subsequence (σ (η k))) + -H.toReal / seq.scale (G.subsequence (σ (η k))) ∈
            (F (G.subsequence (σ (η k)))).time_domain ∧
          baseTime (G.subsequence (σ (η k))) + -H.toReal / seq.scale (G.subsequence (σ (η k))) ∈
            Ico 0 (baseTime (G.subsequence (σ (η k))))) ∧
        (∀ k, ∃ b, ∃ _hb : b ≤ -(H.toReal + d (j k) / 2),
          ∃ e : SurgeryFlowCylinder (F (G.subsequence (σ (η k)))) G.limit.sliceCarrier
              (baseTime (G.subsequence (σ (η k)))) (seq.scale (G.subsequence (σ (η k))))
              (Icc b 0) (G.exhaustion.space (j k)),
            ∀ ht : -H.toReal ∈ Icc b 0,
              ((ψ k : G.limit.sliceCarrier.carrier → _) = e.forward (-H.toReal) ht) ∧
              (((ψ k).symm : _ → G.limit.sliceCarrier.carrier) = e.inverse (-H.toReal) ht)) ∧
        ∀ m, ∀ᶠ k : ℕ in atTop,
          ∃ b, ∃ _hb : b ≤ -(H.toReal + d (j m) / 2),
            ∃ ht : -H.toReal ∈ Icc b 0,
              ∃ e : SurgeryFlowCylinder (F (G.subsequence (σ (η k)))) G.limit.sliceCarrier
                  (baseTime (G.subsequence (σ (η k)))) (seq.scale (G.subsequence (σ (η k))))
                  (Icc b 0) (U (j m)),
                EqOn (ψ k) (e.forward (-H.toReal) ht) (U (j m)) ∧
                (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U (j m),
                  |((F (G.subsequence (σ (η k)))).connection
                    (baseTime (G.subsequence (σ (η k))) +
                      s / seq.scale (G.subsequence (σ (η k))))).curvatureTensorNorm
                    (e.forward s hs x)| ≤ K (j m) * seq.scale (G.subsequence (σ (η k)))) ∧
                ∀ s (_hs : s ∈ Icc (-(H.toReal + d (j m) / 2)) 0)
                  (hs' : s ∈ Icc b 0) (x : U (j m)) (v w : Euc),
                    ((A (j m) (σ (η k))).metric s).inner x v w = e.pullbackInner s hs' x.val
                      (mfderiv (𝓡 3) (𝓡 3)
                        (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x v)
                      (mfderiv (𝓡 3) (𝓡 3)
                        (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x w) := by
  classical
  let seq := regularHistoryBlowupSequence F W history baseTime hbaseTime
    basePoint hPositive hDiverges
  dsimp only
  let h0 : ∀ k, (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    fun k => ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  let Z : ∀ k, G.limit.sliceCarrier.carrier →
      ((F (G.subsequence k)).slice
        (baseTime (G.subsequence k) + 0 / seq.scale (G.subsequence k))).carrier :=
    fun k x => (history (G.subsequence k)).history.forward
      (baseTime (G.subsequence k) + 0 / seq.scale (G.subsequence k))
      (limitNoncollapse_physical_time_mem G k 0 (h0 k))
      ((G.embedding k).forward 0 (h0 k) x)
  let data := fun m k b (e : SurgeryFlowCylinder (F (G.subsequence (σ k))) G.limit.sliceCarrier
      (baseTime (G.subsequence (σ k))) (seq.scale (G.subsequence (σ k)))
      (Icc b 0) (G.exhaustion.space (j m))) =>
    (∀ hzero : 0 ∈ Icc b 0, ∀ x ∈ U (j m), e.forward 0 hzero x = Z (σ k) x) ∧
    (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U (j m),
      |((F (G.subsequence (σ k))).connection
        (baseTime (G.subsequence (σ k)) + s / seq.scale (G.subsequence (σ k)))).curvatureTensorNorm
          (e.forward s hs x)| ≤ K (j m) * seq.scale (G.subsequence (σ k))) ∧
    ∀ s (_hs : s ∈ Icc (-(H.toReal + d (j m) / 2)) 0)
      (hs' : s ∈ Icc b 0) (x : U (j m)) (v w : Euc),
        ((A (j m) (σ k)).metric s).inner x v w = e.pullbackInner s hs' x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x w)
  have havailable (m : ℕ) : ∀ᶠ k : ℕ in atTop,
      ∃ b, b ≤ -(H.toReal + d (j m) / 2) ∧
        ∃ e : SurgeryFlowCylinder (F (G.subsequence (σ k))) G.limit.sliceCarrier
            (baseTime (G.subsequence (σ k))) (seq.scale (G.subsequence (σ k)))
            (Icc b 0) (G.exhaustion.space (j m)), data m k b e := by
    filter_upwards [hσ.tendsto_atTop.eventually (hactual (j m))] with k hk
    obtain ⟨_hI, _hspace, b, hb, e, hmap, hnorm, _hbound, hread, _hold⟩ := hk
    refine ⟨b, hb.le, e, ?_, hnorm, ?_⟩
    · intro hzero x hx
      exact hmap 0 ⟨(hc (j m)).1, le_rfl⟩ hzero x hx
    · intro s hs hs' x v w
      exact hread s hs x v w
  obtain ⟨η, hη, b, hb, E, hE⟩ := limitFinite_endpoint_source_diagonal F
    (fun k => G.subsequence (σ k)) baseTime seq.scale G.exhaustion.space j H.toReal
    (fun m => d (j m)) data havailable
  let n := fun k => G.subsequence (σ (η k))
  have hT : 0 < H.toReal :=
    limitFinite_horizon_pos (by simpa using G.limit.zero_mem.2) hfinite
  obtain ⟨ψ, hsource, hinverse, htime, hrow⟩ := limitFinite_endpoint_physical_maps
    (fun k => F (n k)) (fun k => baseTime (n k)) (fun k => seq.scale (n k))
    G.exhaustion.space G.exhaustion.space_open G.exhaustion.space_increasing j
    (fun k _ hx => hj k (subset_closure hx)) hT (fun m => d (j m)) (fun m => hd (j m))
    (fun k => b k k le_rfl) (fun k => hb k k le_rfl)
    (fun k => E k k le_rfl) (fun k => Z (σ (η k)))
    (fun k hz x hx => (hE k k le_rfl).1 hz x hx)
  refine ⟨η, hη, G.subsequence_strictMono.comp (hσ.comp hη), ψ, hsource, htime, ?_, ?_⟩
  · intro k
    exact ⟨b k k le_rfl, hb k k le_rfl, E k k le_rfl, hinverse k⟩
  · intro m
    filter_upwards [eventually_ge_atTop (max m (j m))] with k hk
    have hmk : m ≤ k := (le_max_left _ _).trans hk
    have hjk : j m ≤ k := (le_max_right _ _).trans hk
    have ht : -H.toReal ∈ Icc (b k m hmk) 0 :=
      ⟨by linarith [hb k m hmk, hd (j m)], neg_nonpos.mpr hT.le⟩
    refine ⟨b k m hmk, hb k m hmk, ht, E k m hmk,
      hrow m k hjk _ (hb k m hmk) (E k m hmk) (hE k m hmk).1 ht,
      (hE k m hmk).2.1, (hE k m hmk).2.2⟩

end PoincareConjecture.M47
