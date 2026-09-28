import PoincareConjecture.Proofs.M47.LimitFiniteActualCandidates
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointCompatibility
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointOldMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance actualCompatDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualCompatDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance actualCompatBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualCompatBilinSpace :
    NormedSpace ℝ Bilin := ContinuousLinearMap.toNormedSpace

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

private local instance actualCompatTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance actualCompatCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance actualCompatManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

local notation "U" => (fun j : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j))

variable (d K : ℕ → ℝ)
  (hc : ∀ j, -H.toReal + d j / 4 ∈ blowupBackwardInterval H)
  (A : ∀ j, ℕ → RicciFlow 3
    (TopologicalSpace.Opens.mk (G.exhaustion.space j) (G.exhaustion.space_open j))
    (Icc (-(H.toReal + d j / 2)) 0))
  (hactual :
    let seq := regularHistoryBlowupSequence F W history baseTime hbaseTime
      basePoint hPositive hDiverges
    let Us := fun j : ℕ => TopologicalSpace.Opens.mk
      (G.exhaustion.space j) (G.exhaustion.space_open j)
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
            (∀ s ∈ Icc (-(H.toReal + d j / 2)) 0, ∀ x : Us j,
              |((A j k).connection s).curvatureTensorNorm x| ≤ K j) ∧
            (∀ s (hs : s ∈ Icc (-(H.toReal + d j / 2)) 0) (x : Us j),
              ∀ v w : TangentSpace (𝓡 3) x,
                ((A j k).metric s).inner x v w = e.pullbackInner s
                  ⟨hb.le.trans hs.1, hs.2⟩ x.val
                  (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Us j → G.limit.sliceCarrier.carrier) x v)
                  (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Us j → G.limit.sliceCarrier.carrier) x w)) ∧
            ∀ s (_hs : s ∈ Icc (-(H.toReal + d j / 2)) 0)
              (hs' : s ∈ Icc (-G.exhaustion.time k) 0) (x : Us j),
              ∀ v w : TangentSpace (𝓡 3) x,
                ((A j k).metric s).inner x v w = (G.embedding k).pullbackInner s hs' x.val
                  (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Us j → G.limit.sliceCarrier.carrier) x v)
                  (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Us j → G.limit.sliceCarrier.carrier) x w))

include hactual hc in

theorem limitFinite_actual_endpoint_pairing
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (j l : ℕ) {t : ℝ}
    (htj : t ∈ Icc (-(H.toReal + d j / 2)) 0)
    (htl : t ∈ Icc (-(H.toReal + d l / 2)) 0)
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E (U j) ∞)
    (Ψ : PartialDiffeomorph (𝓡 3) (𝓡 3) E (U l) ∞) (z w : E)
    (hpoint : (Φ z).val = (Ψ w).val) (v1 u1 v2 u2 : E)
    (hv : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z v1) =
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U l → G.limit.sliceCarrier.carrier) (Ψ w)
        (mfderiv (𝓡 3) (𝓡 3) Ψ w v2))
    (hu : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z u1) =
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U l → G.limit.sliceCarrier.carrier) (Ψ w)
        (mfderiv (𝓡 3) (𝓡 3) Ψ w u2))
    (B1 B2 : Bilin)
    (hconv1 : ∀ v u, Tendsto (fun k =>
      ((A j (σ k)).metric t).pullbackCoefficients Φ z v u) atTop (𝓝 (B1 v u)))
    (hconv2 : ∀ v u, Tendsto (fun k =>
      ((A l (σ k)).metric t).pullbackCoefficients Ψ w v u) atTop (𝓝 (B2 v u))) :
    B1 v1 u1 = B2 v2 u2 := by
  have hpair : ∀ᶠ k in atTop,
      ((A j (σ k)).metric t).pullbackCoefficients Φ z v1 u1 =
        ((A l (σ k)).metric t).pullbackCoefficients Ψ w v2 u2 := by
    filter_upwards [hσ.tendsto_atTop.eventually (hactual j),
      hσ.tendsto_atTop.eventually (hactual l)] with k hj hl
    obtain ⟨hIj, _hspacej, bj, hbj, e, hmapj, _hnormj, _hboundj, hreadj, _holdj⟩ := hj
    obtain ⟨hIl, _hspacel, bl, hbl, f, hmapl, _hnorml, _hboundl, hreadl, _holdl⟩ := hl
    have hI : Icc t 0 ⊆ Icc bj 0 := Icc_subset_Icc (hbj.le.trans htj.1) le_rfl
    have hJ : Icc t 0 ⊆ Icc bl 0 := Icc_subset_Icc (hbl.le.trans htl.1) le_rfl
    have hzero : ∀ x ∈ G.exhaustion.space j ∩ G.exhaustion.space l,
        e.forward 0 (hI ⟨htj.2, le_rfl⟩) x =
          f.forward 0 (hJ ⟨htj.2, le_rfl⟩) x := by
      intro x hx
      exact (hmapj 0 ⟨(hc j).1, le_rfl⟩ _ x hx.1).trans
        (hmapl 0 ⟨(hc l).1, le_rfl⟩ _ x hx.2).symm
    have hx : (Φ z).val ∈ G.exhaustion.space j ∩ G.exhaustion.space l := by
      refine ⟨(Φ z).property, ?_⟩
      rw [hpoint]
      exact (Ψ w).property
    have heq := limitFinite_physical_pullback_eq e f (G.exhaustion.space_open j)
      (G.exhaustion.space_open l) htj.2 hI hJ hzero hx
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z v1))
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z u1))
    have hleft := hreadj t htj (Φ z)
      (mfderiv (𝓡 3) (𝓡 3) Φ z v1) (mfderiv (𝓡 3) (𝓡 3) Φ z u1)
    have hright := hreadl t htl (Ψ w)
      (mfderiv (𝓡 3) (𝓡 3) Ψ w v2) (mfderiv (𝓡 3) (𝓡 3) Ψ w u2)
    change ((A j (σ k)).metric t).pullbackCoefficients Φ z v1 u1 = _ at hleft
    change ((A l (σ k)).metric t).pullbackCoefficients Ψ w v2 u2 = _ at hright
    apply hleft.trans
    apply heq.trans
    rw [hv, hu, hpoint]
    exact hright.symm
  exact tendsto_nhds_unique (hconv1 v1 u1)
    ((hconv2 v2 u2).congr' (hpair.mono fun _ hk => hk.symm))

include hactual in

theorem limitFinite_actual_endpoint_old_metric
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (j : ℕ) {t : ℝ}
    (ht : t ∈ blowupBackwardInterval H)
    (htj : t ∈ Icc (-(H.toReal + d j / 2)) 0)
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E (U j) ∞) (z : E) (B : Bilin)
    (hconv : ∀ v w, Tendsto (fun k =>
      ((A j (σ k)).metric t).pullbackCoefficients Φ z v w) atTop (𝓝 (B v w))) :
    B = ((G.limit.flow.metric t).pullbackOfLocalDiffeomorph
      (Subtype.val : U j → G.limit.sliceCarrier.carrier)
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U j))).pullbackCoefficients Φ z := by
  have hread : ∀ᶠ k : ℕ in atTop,
      ∃ htk : t ∈ Icc (-G.exhaustion.time (σ k)) 0,
        ∀ (x : U j) (v w : TangentSpace (𝓡 3) x),
          ((A j (σ k)).metric t).inner x v w =
            (G.embedding (σ k)).pullbackInner t htk x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) x w) := by
    filter_upwards [hσ.tendsto_atTop.eventually (hactual j),
      hσ.tendsto_atTop.eventually (G.exhaustion.time_cofinal {t} isCompact_singleton
        (singleton_subset_iff.mpr ht))] with k hk htime
    obtain ⟨_hI, _hspace, _b, _hb, _e, _hmap, _hnorm, _hbound, _hread, hold⟩ := hk
    exact ⟨htime (mem_singleton _), fun x v w =>
      hold t htj (htime (mem_singleton _)) x v w⟩
  exact limitFinite_endpoint_old_metric G j σ hσ ht
    (fun k => (A j (σ k)).metric t) hread Φ z B hconv

end PoincareConjecture.M47
