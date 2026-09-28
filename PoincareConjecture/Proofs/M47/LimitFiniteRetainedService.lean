import PoincareConjecture.Proofs.M47.LimitFiniteRetainedScalarCeiling
import PoincareConjecture.Proofs.M47.LimitFiniteRetainedBall










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance retainedServiceDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance retainedServiceDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance retainedServiceBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance retainedServiceBilinSpace :
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

private local instance retainedServiceTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance retainedServiceCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance retainedServiceManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold
private local instance retainedServiceMeasurable : MeasurableSpace G.limit.carrier.carrier :=
  G.limit.carrier.measurableSpace
private local instance retainedServiceBorel : BorelSpace G.limit.carrier.carrier :=
  G.limit.carrier.borelSpace
private local instance retainedServiceT2 : T2Space G.limit.carrier.carrier :=
  G.limit.carrier.t2Space
private local instance retainedServiceT3 : T3Space G.limit.carrier.carrier :=
  G.limit.carrier.t3Space
private local instance retainedServiceSecondCountable :
    SecondCountableTopology G.limit.carrier.carrier := G.limit.carrier.secondCountable
private local instance retainedServiceConnected : ConnectedSpace G.limit.carrier.carrier :=
  G.limit.connectedSpace

local notation "U" => (fun j : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j))




theorem limitFinite_actual_retained_terminal_ball_service
    (P : M47Predecessors.{u}) (sched : RepairedControlledSchedulesData.{u})
    (r : ℕ → ℝ)
    (hfloor : ∀ k, (r k)⁻¹ ^ 2 ≤
      (regularHistoryBlowupSequence F W history baseTime hbaseTime
        basePoint hPositive hDiverges).scale k)
    (hEpsilon : ∀ k, (F k).parameters.epsilon = sched.setup.epsilon)
    (hC : ∀ k, (F k).parameters.C = sched.setup.C)
    (hPast : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (r k))
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
    (j N : ℕ → ℕ) (hj : ∀ m, closure (G.exhaustion.space m) ⊆ G.exhaustion.space (j m))
    (R ρ : ∀ m, Fin (N m + 1) → ℝ) (hρR : ∀ m i, ρ m i < R m i)
    (Φ : ∀ m, Fin (N m + 1) → PartialDiffeomorph (𝓡 3) (𝓡 3) E (U (j m)) ∞)
    (hsource : ∀ m i, (Φ m i).source = Metric.ball 0 (R m i))
    (hcover : ∀ m, closure (G.exhaustion.space m) ⊆
      ⋃ i, (fun z : E => (Φ m i z).val) '' Metric.ball 0 (ρ m i))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (B : ∀ m, Fin (N m + 1) → ℝ × E → Bilin)
    (hB : ∀ m i, ContDiffOn ℝ ∞ (B m i)
      (Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i)))
    (hjets : ∀ m i order C, IsCompact C →
      C ⊆ Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i) →
        TendstoUniformlyOn (fun k => iteratedFDeriv ℝ order (fun p : ℝ × E =>
          ((A (j m) (σ k)).metric (p.1 + (-H.toReal + d (j m) / 4))).pullbackCoefficients
            (Φ m i) p.2)) (iteratedFDeriv ℝ order (B m i)) atTop C)
    (gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier) (DE : LeviCivitaData gE)
    (hcomplete : MetricComplete gE) (hoperator : ∀ x, DE.NonnegativeCurvatureOperator x)
    (hinner : ∀ m i, EqOn (fun z => B m i (-d (j m) / 4, z))
      (gE.pullbackCoefficients (fun z : E => (Φ m i z).val)) (Metric.ball 0 (ρ m i)))
    (hconnected : ∀ m, ConnectedSpace (U m))
    (L : ∀ m, RicciFlow 3 (U m) (Icc (-(d (j m) / 32)) 0))
    (hmetric : ∀ m (x : U m) (v w : E), ((L m).metric 0).inner x v w = gE.inner x.val v w)
    (hlocalOperator : ∀ m t, t ∈ Icc (-(d (j m) / 32)) 0 → ∀ x,
      ((L m).connection t).NonnegativeCurvatureOperator x)
    (htriple : ∀ x y z : G.limit.sliceCarrier.carrier, ∃ m,
      x ∈ U m ∧ y ∈ U m ∧ z ∈ U m) :
    let seq := regularHistoryBlowupSequence F W history baseTime hbaseTime
      basePoint hPositive hDiverges
    ∃ η : ℕ → ℕ, StrictMono η ∧ StrictMono (fun k => G.subsequence (σ (η k))) ∧
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
        ∃ Bglobal : ℝ, 0 < Bglobal ∧ (∀ x, DE.curvatureTensorNorm x ≤ Bglobal) ∧
        let Lscalar := 2 * max 1 (3 * Bglobal)
        1 ≤ Lscalar ∧ ∀ radius : ℝ, 0 < radius →
          let Uball := (G.limit.flow.metric 0).ball G.limit.base radius
          ∀ᶠ k : ℕ in atTop, Uball ⊆ G.exhaustion.space (σ (η k)) ∧
            ∃ e0 : SurgeryFlowCylinder (F (G.subsequence (σ (η k)))) G.limit.sliceCarrier
                (baseTime (G.subsequence (σ (η k)))) (seq.scale (G.subsequence (σ (η k))))
                (Icc (-H.toReal) 0) Uball,
              EqOn (ψ k) (e0.forward (-H.toReal)
                ⟨le_rfl, neg_nonpos.mpr ENNReal.toReal_nonneg⟩) Uball ∧
              (∀ s (hs : s ∈ Icc (-H.toReal) 0)
                (hsG : s ∈ Icc (-G.exhaustion.time (σ (η k))) 0), ∀ x ∈ Uball,
                e0.forward s hs x = (history (G.subsequence (σ (η k)))).history.forward
                  (baseTime (G.subsequence (σ (η k))) + s / seq.scale (G.subsequence (σ (η k))))
                  (limitNoncollapse_physical_time_mem G (σ (η k)) s hsG)
                  ((G.embedding (σ (η k))).forward s hsG x)) ∧
              (∀ s (hs : s ∈ Icc (-H.toReal) 0)
                (hsG : s ∈ Icc (-G.exhaustion.time (σ (η k))) 0), ∀ x ∈ Uball,
                ∀ v w : TangentSpace (𝓡 3) x,
                  e0.pullbackInner s hs x v w =
                    (G.embedding (σ (η k))).pullbackInner s hsG x v w) ∧
              (∀ x ∈ Uball,
                ((F (G.subsequence (σ (η k)))).connection
                  (baseTime (G.subsequence (σ (η k))) +
                    -H.toReal / seq.scale (G.subsequence (σ (η k))))).scalarCurvature
                  (e0.forward (-H.toReal) ⟨le_rfl, neg_nonpos.mpr ENNReal.toReal_nonneg⟩ x) ≤
                    Lscalar * seq.scale (G.subsequence (σ (η k)))) ∧
              (∀ x ∈ Uball, ∀ v : TangentSpace (𝓡 3) x,
                e0.pullbackInner 0 ⟨neg_nonpos.mpr ENNReal.toReal_nonneg, le_rfl⟩ x v v ≤
                  2 * (G.limit.flow.metric 0).inner x v v) ∧
              ((⟨baseTime (G.subsequence (σ (η k))) + 0 / seq.scale (G.subsequence (σ (η k))),
                  e0.forward 0 ⟨neg_nonpos.mpr ENNReal.toReal_nonneg, le_rfl⟩ G.limit.base⟩ :
                  Σ t, ((F (G.subsequence (σ (η k)))).slice t).carrier) =
                ⟨baseTime (G.subsequence (σ (η k))),
                  (history (G.subsequence (σ (η k)))).history.forward
                    (baseTime (G.subsequence (σ (η k)))) (hbaseTime (G.subsequence (σ (η k))))
                    (basePoint (G.subsequence (σ (η k))))⟩) := by
  dsimp only
  obtain ⟨η, hη, hn, ψ, hψsource, htimes, _hinverse, atlas, _hatlasInverse,
    _hatlasDomains, _hatlasCover, _hjet, Bglobal, hBglobal, hbound, hKscalar, hceiling, hrow⟩ :=
    limitFinite_actual_retained_scalar_ceiling F W history baseTime hbaseTime basePoint
      hPositive hDiverges G P sched r hfloor hEpsilon hC hPast hfinite d K hd hc A hactual
      j N hj R ρ hρR Φ hsource hcover σ hσ B hB hjets gE DE hcomplete hoperator hinner
      hconnected L hmetric hlocalOperator htriple
  refine ⟨η, hη, hn, ψ, hψsource, htimes, Bglobal, hBglobal, hbound, by linarith, ?_⟩
  intro radius hradius
  apply limitFinite_eventually_retained_terminal_ball F W history baseTime hbaseTime
    basePoint hPositive hDiverges G σ η hσ hη j hj ψ ?_ (2 * max 1 (3 * Bglobal)) ?_
    radius hradius
  · intro m
    filter_upwards [hrow m] with k hk
    obtain ⟨b, hb, ht, e, hepsi, _henorm, _hemetric, hezero⟩ := hk
    have hbc : b ≤ -H.toReal := by linarith only [hb, hd (j m)]
    exact ⟨b, hbc, e, hepsi, hezero⟩
  · intro C hCcompact
    filter_upwards [hceiling C hCcompact] with k hk
    exact hk.2

end PoincareConjecture.M47
