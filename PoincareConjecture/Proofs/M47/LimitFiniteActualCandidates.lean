import PoincareConjecture.Proofs.M47.LimitFiniteOriginalInterior
import PoincareConjecture.Proofs.M47.LimitNoncollapsePhysicalTime

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

private local instance actualCandidatesTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance actualCandidatesCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance actualCandidatesManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem limitFinite_actual_source_candidates
    (P : M47Predecessors.{u}) (j : ℕ) {d K : ℝ} (hd : 0 < d)
    (hc : -H.toReal + d / 4 ∈ blowupBackwardInterval H)
    (longSources : ∀ᶠ k : ℕ in atTop,
      ∃ hI : Icc (-H.toReal + d / 4) 0 ⊆ Icc (-G.exhaustion.time k) 0,
        G.exhaustion.space j ⊆ G.exhaustion.space k ∧
        ∃ (b : ℝ) (_hb : b < -(H.toReal + d / 2)),
          ∃ E : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
              (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
              (Icc b 0) (G.exhaustion.space j),
            (∀ s (hs : s ∈ Icc (-H.toReal + d / 4) 0) (hs' : s ∈ Icc b 0),
              ∀ x ∈ G.exhaustion.space j,
                E.forward s hs' x = (history (G.subsequence k)).history.forward
                  (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))
                  (limitNoncollapse_physical_time_mem G k s (hI hs))
                  ((G.embedding k).forward s (hI hs) x)) ∧
            ∀ s (hs : s ∈ Icc b 0), ∀ x ∈ G.exhaustion.space j,
              |((F (G.subsequence k)).connection
                (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).curvatureTensorNorm
                  (E.forward s hs x)| ≤ K * (V).scale (G.subsequence k)) :
    let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
      ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
    ∃ A : ℕ → RicciFlow 3 U (Icc (-(H.toReal + d / 2)) 0),
      ∀ᶠ k : ℕ in atTop,
        ∃ hI : Icc (-H.toReal + d / 4) 0 ⊆ Icc (-G.exhaustion.time k) 0,
          G.exhaustion.space j ⊆ G.exhaustion.space k ∧
          ∃ (b : ℝ) (hb : b < -(H.toReal + d / 2)),
            ∃ E : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
                (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
                (Icc b 0) (G.exhaustion.space j),
              (∀ s (hs : s ∈ Icc (-H.toReal + d / 4) 0) (hs' : s ∈ Icc b 0),
                ∀ x ∈ G.exhaustion.space j,
                  E.forward s hs' x = (history (G.subsequence k)).history.forward
                    (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))
                    (limitNoncollapse_physical_time_mem G k s (hI hs))
                    ((G.embedding k).forward s (hI hs) x)) ∧
              (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ G.exhaustion.space j,
                |((F (G.subsequence k)).connection (baseTime (G.subsequence k) +
                  s / (V).scale (G.subsequence k))).curvatureTensorNorm (E.forward s hs x)| ≤
                    K * (V).scale (G.subsequence k)) ∧
              (∀ s ∈ Icc (-(H.toReal + d / 2)) 0, ∀ x : U,
                |((A k).connection s).curvatureTensorNorm x| ≤ K) ∧
              (∀ s (hs : s ∈ Icc (-(H.toReal + d / 2)) 0) (x : U),
                ∀ v w : TangentSpace (𝓡 3) x,
                  ((A k).metric s).inner x v w = E.pullbackInner s
                    ⟨hb.le.trans hs.1, hs.2⟩ x.val
                    (mfderiv (𝓡 3) (𝓡 3)
                      (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
                    (mfderiv (𝓡 3) (𝓡 3)
                      (Subtype.val : U → G.limit.sliceCarrier.carrier) x w)) ∧
              ∀ s (_hs : s ∈ Icc (-(H.toReal + d / 2)) 0)
                (hs' : s ∈ Icc (-G.exhaustion.time k) 0) (x : U),
                ∀ v w : TangentSpace (𝓡 3) x,
                  ((A k).metric s).inner x v w = (G.embedding k).pullbackInner s hs' x.val
                    (mfderiv (𝓡 3) (𝓡 3)
                      (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
                    (mfderiv (𝓡 3) (𝓡 3)
                      (Subtype.val : U → G.limit.sliceCarrier.carrier) x w) := by
  intro U
  let good := fun (k : ℕ) (A : RicciFlow 3 U (Icc (-(H.toReal + d / 2)) 0)) =>
    ∃ hI : Icc (-H.toReal + d / 4) 0 ⊆ Icc (-G.exhaustion.time k) 0,
      G.exhaustion.space j ⊆ G.exhaustion.space k ∧
      ∃ (b : ℝ) (hb : b < -(H.toReal + d / 2)),
        ∃ E : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
            (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
            (Icc b 0) (G.exhaustion.space j),
          (∀ s (hs : s ∈ Icc (-H.toReal + d / 4) 0) (hs' : s ∈ Icc b 0),
            ∀ x ∈ G.exhaustion.space j,
              E.forward s hs' x = (history (G.subsequence k)).history.forward
                (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))
                (limitNoncollapse_physical_time_mem G k s (hI hs))
                ((G.embedding k).forward s (hI hs) x)) ∧
          (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ G.exhaustion.space j,
            |((F (G.subsequence k)).connection
              (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))).curvatureTensorNorm
                (E.forward s hs x)| ≤ K * (V).scale (G.subsequence k)) ∧
          (∀ s ∈ Icc (-(H.toReal + d / 2)) 0, ∀ x : U,
            |(A.connection s).curvatureTensorNorm x| ≤ K) ∧
          (∀ s (hs : s ∈ Icc (-(H.toReal + d / 2)) 0) (x : U),
            ∀ v w : TangentSpace (𝓡 3) x,
              (A.metric s).inner x v w = E.pullbackInner s
                ⟨hb.le.trans hs.1, hs.2⟩ x.val
                (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
                (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) x w)) ∧
          ∀ s (_hs : s ∈ Icc (-(H.toReal + d / 2)) 0)
            (hs' : s ∈ Icc (-G.exhaustion.time k) 0) (x : U),
            ∀ v w : TangentSpace (𝓡 3) x,
              (A.metric s).inner x v w = (G.embedding k).pullbackInner s hs' x.val
                (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
                (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) x w)
  have hgood : ∀ᶠ k : ℕ in atTop, ∃ A, good k A := by
    filter_upwards [longSources] with k hk
    obtain ⟨hI, hspace, b, hb, E, hmap, hcurv⟩ := hk
    have htau : 0 < H.toReal + d / 2 := by
      linarith only [ENNReal.toReal_nonneg (a := H), hd]
    have hzero : ∀ (hE0 : (0 : ℝ) ∈ Icc b 0)
        (he0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0), ∀ x ∈ U,
        E.forward 0 hE0 x = (history (G.subsequence k)).history.forward
          (baseTime (G.subsequence k) + 0 / (V).scale (G.subsequence k))
          (((history (G.subsequence k)).generalized.slice_nonempty_iff _).mp
            ⟨(G.embedding k).forward 0 he0 x⟩)
          ((G.embedding k).forward 0 he0 x) := by
      intro hE0 he0 x hx
      exact hmap 0 ⟨hc.1, le_rfl⟩ hE0 x hx
    obtain ⟨A, hread, hbound, hold⟩ := limitFinite_original_interior_flow P
      (history (G.subsequence k)) U (G.exhaustion.space_open k) hspace
      ⟨G.limit.base, G.exhaustion.base_mem j⟩ (hbaseTime (G.subsequence k))
      (G.exhaustion.time_pos k) htau hb E (G.embedding k) hzero hcurv
    refine ⟨A, hI, hspace, b, hb, E, hmap, hcurv, hbound, ?_, hold⟩
    intro s hs x v w
    exact (hread s hs x).1 v w
  obtain ⟨A, hA⟩ := Filter.Eventually.choice hgood
  refine ⟨A, ?_⟩
  filter_upwards [hA] with k hk
  obtain ⟨hI, hspace, b, hb, E, hmap, hcurv, hbound, hread, hold⟩ := hk
  exact ⟨hI, hspace, b, hb, E, hmap, hcurv, hbound, hread, hold⟩

end PoincareConjecture.M47
