import PoincareConjecture.Proofs.M47.LimitFiniteActualGermsCompatibility
import PoincareConjecture.Proofs.M47.LimitFiniteActualExtraction
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointStageFlow
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointStageAgreement









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance actualGermsDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualGermsDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance actualGermsBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualGermsBilinSpace :
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

private local instance actualGermsTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance actualGermsCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance actualGermsManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

local notation "U" => (fun j : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j))



theorem limitFinite_actual_endpoint_germs
    (d K : ℕ → ℝ) (hd : ∀ j, 0 < d j)
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
            (Φ m i) p.2)) (iteratedFDeriv ℝ r (B m i)) atTop C)
    (hpoint : ∀ m i p,
      p ∈ Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i) →
        Tendsto (fun k =>
          ((A (j m) (σ k)).metric (p.1 + (-H.toReal + d (j m) / 4))).pullbackCoefficients
            (Φ m i) p.2) atTop (𝓝 (B m i p)))
    (hsymm : ∀ m i p,
      p ∈ Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i) →
        ∀ v w, B m i p v w = B m i p w v)
    (hlower : ∀ m i, ∃ a : ℝ, 0 < a ∧
      ∀ p ∈ Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i),
        ∀ v : E, a * ‖v‖ ^ 2 ≤ B m i p v v) :
    let Wb := fun p : Σ m, Fin (N m + 1) => Metric.ball (0 : E) (ρ p.1 p.2)
    let hWb : ∀ p, IsOpen (Wb p) := fun _ => Metric.isOpen_ball
    letI : ∀ p, Nonempty (Piece Wb p) := fun p => ⟨⟨0, Metric.mem_ball_self (hρ p.1 p.2)⟩⟩
    letI : ∀ p, ChartedSpace E (Piece Wb p) :=
      fun p => (hWb p).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ p, IsManifold (𝓡 3) ∞ (Piece Wb p) :=
      fun p => (hWb p).isOpenEmbedding_subtypeVal.isManifold_singleton
    let q : ∀ m i, Piece Wb ⟨m, i⟩ → G.limit.sliceCarrier.carrier :=
      fun m i x => (Φ m i x).val
    ∃ Fc : ∀ m i, RicciFlow 3 (Piece Wb ⟨m, i⟩)
        (Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4)),
      ∃ Ag : ∀ m, RicciFlow 3 (U m)
          (Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4)),
        (∀ m, -H.toReal ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4)) ∧
        (∀ m t, t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) →
          ∀ i (x : Piece Wb ⟨m, i⟩) (v w : E),
            ((Fc m i).metric t).inner x v w =
              B m i (t - (-H.toReal + d (j m) / 4), x) v w) ∧
        (∀ m t, t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) →
          ∀ i (x : Piece Wb ⟨m, i⟩) (hx : q m i x ∈ U m) (v w : E),
            ((Fc m i).metric t).inner x v w = ((Ag m).metric t).inner ⟨q m i x, hx⟩
              (mfderiv (𝓡 3) (𝓡 3) (q m i) x v)
              (mfderiv (𝓡 3) (𝓡 3) (q m i) x w)) ∧
        (∀ m t, t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) →
          t ∈ blowupBackwardInterval H → ∀ (x : U m) (v w : E),
            ((Ag m).metric t).inner x v w = (G.limit.flow.metric t).inner x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w)) ∧
        ∀ m n t,
          t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) →
          t ∈ Ioo (-H.toReal - d (j n) / 8) (-H.toReal + d (j n) / 4) →
          ∀ (y : G.limit.sliceCarrier.carrier) (hym : y ∈ U m) (hyn : y ∈ U n) (v w : E),
            ((Ag m).metric t).inner ⟨y, hym⟩ v w =
              ((Ag n).metric t).inner ⟨y, hyn⟩ v w := by
  classical
  let Wb := fun p : Σ m, Fin (N m + 1) => Metric.ball (0 : E) (ρ p.1 p.2)
  let hWb : ∀ p, IsOpen (Wb p) := fun _ => Metric.isOpen_ball
  let : ∀ p, Nonempty (Piece Wb p) := fun p => ⟨⟨0, Metric.mem_ball_self (hρ p.1 p.2)⟩⟩
  let : ∀ p, ChartedSpace E (Piece Wb p) :=
    fun p => (hWb p).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ p, IsManifold (𝓡 3) ∞ (Piece Wb p) :=
    fun p => (hWb p).isOpenEmbedding_subtypeVal.isManifold_singleton
  let q : ∀ m i, Piece Wb ⟨m, i⟩ → G.limit.sliceCarrier.carrier :=
    fun m i x => (Φ m i x).val
  change ∃ Fc, ∃ Ag, _
  have htime (m : ℕ) {t : ℝ}
      (ht : t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4)) :
      t ∈ Icc (-(H.toReal + d (j m) / 2)) 0 := by
    constructor
    · linarith [ht.1, hd (j m)]
    · exact ht.2.le.trans (hc (j m)).1
  have hcv (m : ℕ) (i : Fin (N m + 1)) {t : ℝ}
      (ht : t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4))
      (z : E) (hz : z ∈ Metric.ball 0 (ρ m i)) (v w : E) :
      Tendsto (fun k => ((A (j m) (σ k)).metric t).pullbackCoefficients (Φ m i) z v w)
        atTop (𝓝 (B m i (t - (-H.toReal + d (j m) / 4), z) v w)) := by
    have hp : (t - (-H.toReal + d (j m) / 4), z) ∈
        Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i) := by
      refine ⟨⟨?_, ?_⟩, hz⟩ <;> linarith [ht.1, ht.2]
    have h := ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).continuous.tendsto _).comp
        (hpoint m i _ hp))
    simpa only [sub_add_cancel, Function.comp_def, ContinuousLinearMap.apply_apply] using h
  have hpair (m n : ℕ) (t : ℝ)
      (htm : t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4))
      (htn : t ∈ Ioo (-H.toReal - d (j n) / 8) (-H.toReal + d (j n) / 4))
      (i : Fin (N m + 1)) (l : Fin (N n + 1))
      (x : Piece Wb ⟨m, i⟩) (y : Piece Wb ⟨n, l⟩)
      (hxy : (Φ m i x).val = (Φ n l y).val) (a b c e : E)
      (ha : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier)
          (Φ m i x) (mfderiv (𝓡 3) (𝓡 3) (Φ m i) (x : E) a) =
        mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j n) → G.limit.sliceCarrier.carrier)
          (Φ n l y) (mfderiv (𝓡 3) (𝓡 3) (Φ n l) (y : E) c))
      (hb : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier)
          (Φ m i x) (mfderiv (𝓡 3) (𝓡 3) (Φ m i) (x : E) b) =
        mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j n) → G.limit.sliceCarrier.carrier)
          (Φ n l y) (mfderiv (𝓡 3) (𝓡 3) (Φ n l) (y : E) e)) :
      B m i (t - (-H.toReal + d (j m) / 4), x) a b =
        B n l (t - (-H.toReal + d (j n) / 4), y) c e := by
    exact limitFinite_actual_endpoint_pairing F W history baseTime hbaseTime basePoint
      hPositive hDiverges G d K hc A hactual σ hσ (j m) (j n) (htime m htm) (htime n htn)
      (Φ m i) (Φ n l) x y hxy a b c e ha hb _ _
      (hcv m i htm x x.property) (hcv n l htn y y.property)
  have hcharts (m : ℕ) (i : Fin (N m + 1)) :
      ∃ Fc : RicciFlow 3 (Piece Wb ⟨m, i⟩)
          (Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4)),
        -H.toReal ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) ∧
        ∀ t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4),
          ∀ (x : Piece Wb ⟨m, i⟩) (v w : E),
            (Fc.metric t).inner x v w = B m i (t - (-H.toReal + d (j m) / 4), x) v w := by
    obtain ⟨a, ha, hl⟩ := hlower m i
    exact limitFinite_endpoint_chart_flow (hd (j m)) (hc (j m)).1 (hρ m i) (hρR m i) ha
      (fun k => A (j m) (σ k)) (Φ m i) (hsource m i) (B m i) (hB m i)
      (hsymm m i) hl (hjets m i)
  choose Fc hT hcoeff using hcharts
  have hstages (m : ℕ) : ∃ Ag : RicciFlow 3 (U m)
        (Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4)),
      -H.toReal ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4) ∧
      (∀ t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4),
        ∀ i (x : Piece Wb ⟨m, i⟩) (hx : q m i x ∈ U m) (v w : E),
          ((Fc m i).metric t).inner x v w = (Ag.metric t).inner ⟨q m i x, hx⟩
            (mfderiv (𝓡 3) (𝓡 3) (q m i) x v) (mfderiv (𝓡 3) (𝓡 3) (q m i) x w)) ∧
      ∀ t ∈ Ioo (-H.toReal - d (j m) / 8) (-H.toReal + d (j m) / 4),
        t ∈ blowupBackwardInterval H → ∀ (x : U m) (v w : E),
          (Ag.metric t).inner x v w = (G.limit.flow.metric t).inner x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w) := by
    apply limitFinite_endpoint_original_stage_flow G m (j m) (N m) (d (j m))
      (hd (j m)) (R m) (ρ m) (hρ m) (hρR m) (Φ m) (hsource m) (hcover m) (B m)
      (Fc m) (fun t ht i => hcoeff m i t ht)
    · intro t ht i l x y hxy a b c e ha hb
      exact hpair m m t ht ht i l x y hxy a b c e ha hb
    · intro t ht htOld i x
      exact limitFinite_actual_endpoint_old_metric F W history baseTime hbaseTime basePoint
        hPositive hDiverges G d K A hactual σ hσ (j m) htOld (htime m ht)
        (Φ m i) x _ (hcv m i ht x x.property)
  choose Ag hTime hread hold using hstages
  refine ⟨Fc, Ag, hTime, (fun m t ht i => hcoeff m i t ht), hread, hold, ?_⟩
  intro m n t htm htn y hym hyn v w
  have hsub (r : ℕ) (i : Fin (N r + 1)) : Wb ⟨r, i⟩ ⊆ (Φ r i).source := by
    rw [hsource r i]
    exact Metric.ball_subset_ball (hρR r i).le
  obtain ⟨hqm, hdm, _him⟩ := limitFinite_endpoint_chart_maps (fun _ => U (j m))
    (fun i => Wb ⟨m, i⟩) (fun i => hWb ⟨m, i⟩) (Φ m) (hsub m)
  obtain ⟨hqn, hdn, _hin⟩ := limitFinite_endpoint_chart_maps (fun _ => U (j n))
    (fun i => Wb ⟨n, i⟩) (fun i => hWb ⟨n, i⟩) (Φ n) (hsub n)
  have hcoverq (r : ℕ) : ∀ z ∈ U r, ∃ i x, q r i x = z := by
    intro z hz
    obtain ⟨i, x, hx, heq⟩ := mem_iUnion.mp (hcover r (subset_closure hz))
    exact ⟨i, ⟨x, hx⟩, heq⟩
  apply limitFinite_endpoint_stage_agreement (U m) (U n) (q m) (q n)
    hqm hqn (hcoverq m) (hcoverq n)
    (fun i => (Fc m i).metric t) (fun i => (Fc n i).metric t)
    ((Ag m).metric t) ((Ag n).metric t) (hread m t htm) (hread n t htn) ?_
    y hym hyn v w
  intro i l x z hxz a b c e ha hb
  rw [hcoeff m i t htm, hcoeff n l t htn]
  apply hpair m n t htm htn i l x z hxz a b c e
  · exact (hdm i x a).symm.trans (ha.trans (hdn l z c))
  · exact (hdm i x b).symm.trans (hb.trans (hdn l z e))

end PoincareConjecture.M47
