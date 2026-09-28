import PoincareConjecture.Proofs.M47.LimitFiniteActualGerms
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointCurvature
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointChartReadout
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointSignedGerms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance actualMetricDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualMetricDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance actualMetricBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualMetricBilinSpace :
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

private local instance actualMetricTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance actualMetricCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance actualMetricManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold
private local instance actualMetricT3 : T3Space G.limit.carrier.carrier :=
  G.limit.carrier.t3Space

local notation "U" => (fun j : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j))

theorem limitFinite_actual_endpoint_metric
    (P : M47Predecessors.{u}) (hfinite : H ≠ ⊤)
    (hPinched : ∀ k, SurgeryFlowPinched (F k))
    (d K : ℕ → ℝ) (hd : ∀ j, 0 < d j) (hK : ∀ j, 0 ≤ K j)
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
    (j N : ℕ → ℕ) (R ρ : ∀ m, Fin (N m + 1) → ℝ)
    (hρ : ∀ m i, 0 < ρ m i) (hρR : ∀ m i, ρ m i < R m i)
    (Φ : ∀ m, Fin (N m + 1) → PartialDiffeomorph (𝓡 3) (𝓡 3) E (U (j m)) ∞)
    (hsource : ∀ m i, (Φ m i).source = Metric.ball 0 (R m i))
    (hcover : ∀ m, closure (G.exhaustion.space m) ⊆
      ⋃ i, (fun z : E => (Φ m i z).val) '' Metric.ball 0 (ρ m i))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (B : ∀ m, Fin (N m + 1) → ℝ × E → Bilin)
    (hB : ∀ m i, ContDiffOn ℝ ∞ (B m i)
      (Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i)))
    (hjets : ∀ m i r C, IsCompact C →
      C ⊆ Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i) →
        TendstoUniformlyOn (fun k => iteratedFDeriv ℝ r (fun p : ℝ × E =>
          ((A (j m) (σ k)).metric (p.1 + (-H.toReal + d (j m) / 4))).pullbackCoefficients
            (Φ m i) p.2)) (iteratedFDeriv ℝ r (B m i)) atTop C) :
    let Wb := fun p : Σ m, Fin (N m + 1) => Metric.ball (0 : E) (ρ p.1 p.2)
    let hWb : ∀ p, IsOpen (Wb p) := fun _ => Metric.isOpen_ball
    letI : ∀ p, Nonempty (Piece Wb p) := fun p => ⟨⟨0, Metric.mem_ball_self (hρ p.1 p.2)⟩⟩
    letI : ∀ p, ChartedSpace E (Piece Wb p) :=
      fun p => (hWb p).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ p, IsManifold (𝓡 3) ∞ (Piece Wb p) :=
      fun p => (hWb p).isOpenEmbedding_subtypeVal.isManifold_singleton
    let q : ∀ m i, Piece Wb ⟨m, i⟩ → G.limit.sliceCarrier.carrier :=
      fun m i x => (Φ m i x).val
    ∀ Fc : ∀ m i, RicciFlow 3 (Piece Wb ⟨m, i⟩)
        (Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4)),
      (∀ m t, t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) →
        ∀ i (x : Piece Wb ⟨m, i⟩) (v w : E),
          ((Fc m i).metric t).inner x v w =
            B m i (t - (-H.toReal + d (j m) / 4), x) v w) →
      ∀ Ag : ∀ m, RicciFlow 3 (U m)
          (Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4)),
        (∀ m t, t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) →
          ∀ i (x : Piece Wb ⟨m, i⟩) (hx : q m i x ∈ U m) (v w : E),
            ((Fc m i).metric t).inner x v w = ((Ag m).metric t).inner ⟨q m i x, hx⟩
              (mfderiv (𝓡 3) (𝓡 3) (q m i) x v)
              (mfderiv (𝓡 3) (𝓡 3) (q m i) x w)) →
        (∀ m t, t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) →
          t ∈ blowupBackwardInterval H → ∀ (x : U m) (v w : E),
            ((Ag m).metric t).inner x v w = (G.limit.flow.metric t).inner x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w)) →
        (∀ m n t,
          t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) →
          t ∈ Ioo (-H.toReal - d (j n) / 8) (-H.toReal + d (j n) / 4) →
          ∀ (y : G.limit.sliceCarrier.carrier) (hym : y ∈ U m) (hyn : y ∈ U n) (v w : E),
            ((Ag m).metric t).inner ⟨y, hym⟩ v w =
              ((Ag n).metric t).inner ⟨y, hyn⟩ v w) →
        ∃ gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier, ∃ DE : LeviCivitaData gE,
          MetricComplete gE ∧
          (∀ (x : G.limit.sliceCarrier.carrier) (v : E),
            (G.limit.flow.metric 0).inner x v v ≤ gE.inner x v v) ∧
          (∀ x, DE.NonnegativeCurvatureOperator x) ∧
          (∀ m (x : U m) (v w : E), ((Ag m).metric (-H.toReal)).inner x v w =
            gE.inner x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w)) ∧
          (∀ m (x : U m) (v w : E), ((Ag m).metric (-H.toReal)).inner x v w =
            gE.inner x.val v w) ∧
          (∀ m i, EqOn (fun z => B m i (-d (j m) / 4, z))
            (gE.pullbackCoefficients (fun z : E => (Φ m i z).val)) (Metric.ball 0 (ρ m i))) ∧
          (∀ m, ConnectedSpace (U m)) ∧
          (∀ x y z : G.limit.sliceCarrier.carrier, ∃ m,
            x ∈ U m ∧ y ∈ U m ∧ z ∈ U m) ∧
          ∃ L : ∀ m, RicciFlow 3 (U m) (Icc (-(d (j m) / 32)) 0),
            (∀ m, 0 < d (j m) / 32) ∧
            (∀ m s, (L m).metric s = (Ag m).metric (s - H.toReal)) ∧
            (∀ m (x : U m) (v w : E), ((L m).metric 0).inner x v w = gE.inner x.val v w) ∧
            ∀ m s, s ∈ Icc (-(d (j m) / 32)) 0 → ∀ x,
              ((L m).connection s).NonnegativeCurvatureOperator x := by
  classical
  let seq := regularHistoryBlowupSequence F W history baseTime hbaseTime
    basePoint hPositive hDiverges
  let Wb := fun p : Σ m, Fin (N m + 1) => Metric.ball (0 : E) (ρ p.1 p.2)
  let hWb : ∀ p, IsOpen (Wb p) := fun _ => Metric.isOpen_ball
  let : ∀ p, Nonempty (Piece Wb p) := fun p => ⟨⟨0, Metric.mem_ball_self (hρ p.1 p.2)⟩⟩
  let : ∀ p, ChartedSpace E (Piece Wb p) :=
    fun p => (hWb p).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ p, IsManifold (𝓡 3) ∞ (Piece Wb p) :=
    fun p => (hWb p).isOpenEmbedding_subtypeVal.isManifold_singleton
  dsimp only
  intro Fc hcoeff Ag hread hold hcompat
  have hT (m : ℕ) : -H.toReal ∈
      Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) :=
    ⟨by linarith [hd (j m)], by linarith [hd (j m)]⟩
  obtain ⟨_ht, gE, DE, hterminal⟩ := limitFinite_exists_endpoint_metric G
    (fun m => d (j m)) (fun m => hd (j m)) Ag
    (fun m n => hcompat m n (-H.toReal) (hT m) (hT n))
  obtain ⟨hfloor, hcomplete⟩ := limitFinite_endpoint_complete G P.m04 hfinite
    (fun m => d (j m)) (fun m => hd (j m)) Ag gE hterminal hold
  have hop := limitFinite_endpoint_operator G (fun m => d (j m)) Ag gE DE
    hterminal hold hfinite (fun m => hd (j m))
  have hterminalFlat : ∀ m (x : U m) (v w : E),
      ((Ag m).metric (-H.toReal)).inner x v w = gE.inner x.val v w := by
    intro m x v w
    simpa only [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply]
      using hterminal m x v w
  have holdFlat : ∀ m t,
      t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) →
      t ∈ blowupBackwardInterval H → ∀ (x : U m) (v w : E),
        ((Ag m).metric t).inner x v w = (G.limit.flow.metric t).inner x.val v w := by
    intro m t ht htOld x v w
    simpa only [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply]
      using hold m t ht htOld x v w
  have hrowOld (m : ℕ) (t : ℝ)
      (ht : t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4))
      (htOld : t ∈ blowupBackwardInterval H) :
      ∀ᶠ k : ℕ in atTop,
        ∃ htk : t ∈ Icc (-G.exhaustion.time (σ k)) 0,
          ∀ (x : U (j m)) (v w : E), ((A (j m) (σ k)).metric t).inner x v w =
            (G.embedding (σ k)).pullbackInner t htk x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x w) := by
    have htA : t ∈ Icc (-(H.toReal + d (j m) / 2)) 0 :=
      ⟨by linarith [ht.1, hd (j m)], htOld.1⟩
    filter_upwards [hσ.tendsto_atTop.eventually (hactual (j m)),
      hσ.tendsto_atTop.eventually (G.exhaustion.time_cofinal {t} isCompact_singleton
        (singleton_subset_iff.mpr htOld))] with k hk htime
    obtain ⟨_hI, _hspace, _b, _hb, _e, _hmap, _hnorm, _hbound, _hread, hkold⟩ := hk
    exact ⟨htime (mem_singleton _), fun x v w => hkold t htA (htime (mem_singleton _)) x v w⟩
  have hinner (m : ℕ) (i : Fin (N m + 1)) :
      EqOn (fun z => B m i (-d (j m) / 4, z))
        (gE.pullbackCoefficients (fun z : E => (Φ m i z).val)) (Metric.ball 0 (ρ m i)) :=
    limitFinite_endpoint_inner_chart_metric G hfinite (fun m => d (j m))
      (fun m => hd (j m)) Ag gE hterminalFlat holdFlat (j m) (hd (j m)) (hρR m i)
      (Φ m i) (hsource m i) (A (j m)) σ hσ (hrowOld m) (B m i) (hB m i) (hjets m i)
  have hphysical (m : ℕ) : ∀ᶠ k in atTop,
      ∃ b, ∃ hb : b ≤ -(H.toReal + d (j m) / 2),
        ∃ e : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
            (baseTime (G.subsequence k)) (seq.scale (G.subsequence k))
            (Icc b 0) (U (j m)),
          (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U (j m),
            |((F (G.subsequence k)).connection
              (baseTime (G.subsequence k) + s / seq.scale (G.subsequence k))).curvatureTensorNorm
                (e.forward s hs x)| ≤ K (j m) * seq.scale (G.subsequence k)) ∧
          ∀ s (hs : s ∈ Icc (-(H.toReal + d (j m) / 2)) 0) (x : U (j m)), ∀ v w : E,
            ((A (j m) k).metric s).inner x v w = e.pullbackInner s
              ⟨hb.trans hs.1, hs.2⟩ x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x w) := by
    filter_upwards [hactual (j m)] with k hk
    obtain ⟨_hI, _hspace, b, hb, e, _hmap, hnorm, _hbound, hm, _hold⟩ := hk
    exact ⟨b, hb.le, e, hnorm, hm⟩
  obtain ⟨hconnected, htriple, L, hLpos, hLmetric, hLend, hLop⟩ :=
    limitFinite_endpoint_original_signed_germs G F hPinched baseTime seq.scale
      seq.scalar_diverges σ hσ j N (fun m => d (j m)) (fun m => K (j m))
      (fun m => hd (j m)) (fun m => hK (j m)) (fun m => (hc (j m)).1)
      (fun m => A (j m)) hphysical R ρ hρ hρR Φ hsource hcover B hjets
      Fc hcoeff Ag hread gE hterminalFlat
  exact ⟨gE, DE, hcomplete, hfloor, hop, hterminal, hterminalFlat, hinner,
    hconnected, htriple, L, hLpos, hLmetric, hLend, hLop⟩

end PoincareConjecture.M47
