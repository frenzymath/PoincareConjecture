import PoincareConjecture.Proofs.M47.LimitFiniteActualRetainedBound
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointScalarCeiling










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance retainedScalarDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance retainedScalarDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance retainedScalarBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance retainedScalarBilinSpace :
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

private local instance retainedScalarTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance retainedScalarCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance retainedScalarManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold
private local instance retainedScalarMeasurable : MeasurableSpace G.limit.carrier.carrier :=
  G.limit.carrier.measurableSpace
private local instance retainedScalarBorel : BorelSpace G.limit.carrier.carrier :=
  G.limit.carrier.borelSpace
private local instance retainedScalarT2 : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
private local instance retainedScalarT3 : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance retainedScalarSecondCountable :
    SecondCountableTopology G.limit.carrier.carrier := G.limit.carrier.secondCountable
private local instance retainedScalarConnected : ConnectedSpace G.limit.carrier.carrier :=
  G.limit.connectedSpace

local notation "U" => (fun j : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j))




theorem limitFinite_actual_retained_scalar_ceiling
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
    let Z : ∀ k, G.limit.sliceCarrier.carrier →
        ((F (G.subsequence k)).slice
          (baseTime (G.subsequence k) + 0 / seq.scale (G.subsequence k))).carrier :=
      fun k x => (history (G.subsequence k)).history.forward
        (baseTime (G.subsequence k) + 0 / seq.scale (G.subsequence k))
        (limitNoncollapse_physical_time_mem G k 0
          ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩)
        ((G.embedding k).forward 0
          ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩ x)
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
        (∀ k, ∃ b, ∃ _hb : b ≤ -(H.toReal + d (j k) / 2),
          ∃ e : SurgeryFlowCylinder (F (G.subsequence (σ (η k)))) G.limit.sliceCarrier
              (baseTime (G.subsequence (σ (η k)))) (seq.scale (G.subsequence (σ (η k))))
              (Icc b 0) (G.exhaustion.space (j k)),
            ∀ ht : -H.toReal ∈ Icc b 0,
              ((ψ k : G.limit.sliceCarrier.carrier → _) = e.forward (-H.toReal) ht) ∧
              (((ψ k).symm : _ → G.limit.sliceCarrier.carrier) = e.inverse (-H.toReal) ht)) ∧
        ∃ c : (Σ m, Fin (N m + 1)) →
            PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.sliceCarrier.carrier E ∞,
          (∀ p, ((c p).symm : E → G.limit.sliceCarrier.carrier) =
            fun z => (Φ p.1 p.2 z).val) ∧
          (∀ p, (c p).source =
              (fun z : E => (Φ p.1 p.2 z).val) '' Metric.ball 0 (ρ p.1 p.2) ∧
            (c p).target = Metric.ball 0 (ρ p.1 p.2)) ∧
          (∀ x, ∃ p, x ∈ (c p).source) ∧
          (∀ p order C, IsCompact C → C ⊆ (c p).target → TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ order
              ((rescaledMetric ((F (G.subsequence (σ (η k)))).metric
                  (baseTime (G.subsequence (σ (η k))) +
                    -H.toReal / seq.scale (G.subsequence (σ (η k)))))
                  (seq.scale (G.subsequence (σ (η k))))
                  (seq.base_scalar_pos (G.subsequence (σ (η k))))).pullbackCoefficients
                (ψ k ∘ (c p).symm)))
            (iteratedFDeriv ℝ order (gE.pullbackCoefficients (c p).symm)) atTop C) ∧
          ∃ Bglobal : ℝ, 0 < Bglobal ∧ (∀ x, DE.curvatureTensorNorm x ≤ Bglobal) ∧
          let Kscalar := max 1 (3 * Bglobal)
          1 ≤ Kscalar ∧
          (∀ V : Set G.limit.sliceCarrier.carrier, IsCompact V → ∀ᶠ k in atTop,
            V ⊆ (ψ k).source ∧ ∀ x ∈ V,
              ((F (G.subsequence (σ (η k)))).connection
                (baseTime (G.subsequence (σ (η k))) +
                  -H.toReal / seq.scale (G.subsequence (σ (η k))))).scalarCurvature (ψ k x) ≤
                    (2 * Kscalar) * seq.scale (G.subsequence (σ (η k)))) ∧
          ∀ m, ∀ᶠ k : ℕ in atTop,
            ∃ b, ∃ _hb : b ≤ -(H.toReal + d (j m) / 2),
              ∃ ht : -H.toReal ∈ Icc b 0,
                ∃ e : SurgeryFlowCylinder (F (G.subsequence (σ (η k)))) G.limit.sliceCarrier
                    (baseTime (G.subsequence (σ (η k))))
                    (seq.scale (G.subsequence (σ (η k))))
                    (Icc b 0) (U (j m)),
                  EqOn (ψ k) (e.forward (-H.toReal) ht) (U (j m)) ∧
                  (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U (j m),
                    |((F (G.subsequence (σ (η k)))).connection
                      (baseTime (G.subsequence (σ (η k))) +
                        s / seq.scale (G.subsequence (σ (η k))))).curvatureTensorNorm
                      (e.forward s hs x)| ≤ K (j m) * seq.scale (G.subsequence (σ (η k)))) ∧
                  (∀ s (_hs : s ∈ Icc (-(H.toReal + d (j m) / 2)) 0)
                    (hs' : s ∈ Icc b 0) (x : U (j m)) (v w : E),
                      ((A (j m) (σ (η k))).metric s).inner x v w = e.pullbackInner s hs' x.val
                        (mfderiv (𝓡 3) (𝓡 3)
                          (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x v)
                        (mfderiv (𝓡 3) (𝓡 3)
                          (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x w)) ∧
                  (∀ hzero : 0 ∈ Icc b 0, ∀ x ∈ U (j m),
                    e.forward 0 hzero x = Z (σ (η k)) x) := by
  dsimp only
  obtain ⟨η, hη, hn, ψ, hψsource, htimes, hinverse, c, hcinverse, hcchart, hcoverC,
    hjet, Bglobal, hBglobal, hbound, hrow⟩ :=
    limitFinite_actual_endpoint_retained_bound F W history baseTime hbaseTime basePoint
      hPositive hDiverges G P sched r hfloor hEpsilon hC hPast hfinite d K hd hc A hactual
      j N hj R ρ hρR Φ hsource hcover σ hσ B hB hjets gE DE hcomplete hoperator hinner
      hconnected L hmetric hlocalOperator htriple
  have hceiling := limitFinite_endpoint_scalar_ceiling F W history baseTime hbaseTime
    basePoint hPositive hDiverges G σ η gE DE hbound ψ hψsource c hcoverC
    (fun i m _hm C hCcompact hCtarget => hjet i m C hCcompact hCtarget)
  exact ⟨η, hη, hn, ψ, hψsource, htimes, hinverse, c, hcinverse, hcchart, hcoverC,
    hjet, Bglobal, hBglobal, hbound, hceiling.1, hceiling.2, hrow⟩

end PoincareConjecture.M47
