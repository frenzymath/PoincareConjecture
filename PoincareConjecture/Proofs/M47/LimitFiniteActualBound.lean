import PoincareConjecture.Proofs.M47.LimitFiniteActualBoundJets
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointHighPoints










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance actualBoundDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualBoundDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance actualBoundBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualBoundBilinSpace :
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

private local instance actualBoundTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance actualBoundCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance actualBoundManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold
private local instance actualBoundMeasurable : MeasurableSpace G.limit.carrier.carrier :=
  G.limit.carrier.measurableSpace
private local instance actualBoundBorel : BorelSpace G.limit.carrier.carrier :=
  G.limit.carrier.borelSpace
private local instance actualBoundT2 : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
private local instance actualBoundT3 : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance actualBoundSecondCountable :
    SecondCountableTopology G.limit.carrier.carrier := G.limit.carrier.secondCountable
private local instance actualBoundConnected : ConnectedSpace G.limit.carrier.carrier :=
  G.limit.connectedSpace

local notation "U" => (fun j : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j))



theorem limitFinite_actual_endpoint_bound
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
          ∃ Bglobal : ℝ, 0 < Bglobal ∧ ∀ x, DE.curvatureTensorNorm x ≤ Bglobal := by
  classical
  let seq := regularHistoryBlowupSequence F W history baseTime hbaseTime
    basePoint hPositive hDiverges
  let : ∀ m, ConnectedSpace (U m) := hconnected
  let : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
  dsimp only
  obtain ⟨η, hη, hn, ψ, hψsource, htimes, hinverse, hrow⟩ :=
    limitFinite_actual_endpoint_physical_maps F W history baseTime hbaseTime basePoint
      hPositive hDiverges G hfinite d K hd hc A hactual j hj σ hσ
  let n := fun k => G.subsequence (σ (η k))
  have hphysical (m : ℕ) : ∀ᶠ k : ℕ in atTop,
      ∃ b, ∃ ht : -H.toReal ∈ Icc b 0,
        ∃ e : SurgeryFlowCylinder (F (n k)) G.limit.sliceCarrier
            (baseTime (n k)) (seq.scale (n k)) (Icc b 0) (U (j m)),
          EqOn (ψ k) (e.forward (-H.toReal) ht) (U (j m)) ∧
          ∀ (x : U (j m)) (v w : E),
            ((A (j m) (σ (η k))).metric (-H.toReal)).inner x v w =
              e.pullbackInner (-H.toReal) ht x.val
                (mfderiv (𝓡 3) (𝓡 3)
                  (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x v)
                (mfderiv (𝓡 3) (𝓡 3)
                  (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x w) := by
    filter_upwards [hrow m] with k hk
    obtain ⟨b, _hb, ht, e, hmap, _hnorm, hread⟩ := hk
    have htA : -H.toReal ∈ Icc (-(H.toReal + d (j m) / 2)) 0 :=
      ⟨by linarith [hd (j m)], neg_nonpos.mpr ENNReal.toReal_nonneg⟩
    exact ⟨b, ht, e, hmap, fun x v w => hread (-H.toReal) htA ht x v w⟩
  obtain ⟨c, hcinverse, hcchart, hcoverC, hjet⟩ := limitFinite_actual_endpoint_jets G
    F baseTime seq.scale seq.base_scalar_pos j N (fun m => d (j m))
    (fun m => hd (j m)) (fun m => (hc (j m)).1) (fun m => A (j m))
    σ η hη ψ hphysical R ρ hρR Φ hsource hcover B hB hjets gE hinner
  obtain ⟨Bglobal, hBglobal, hbound⟩ := limitFinite_endpoint_global_bound sched
    (fun k => F (n k)) (fun k => baseTime (n k))
    (fun k => baseTime (n k) + -H.toReal / seq.scale (n k))
    (fun k => seq.scale (n k)) (fun k => r (n k)) (fun k => seq.base_scalar_pos (n k))
    (fun k => hfloor (n k)) (fun k => hEpsilon (n k)) (fun k => hC (n k))
    (fun k => hPast (n k)) (fun k => (htimes k).2.2) (fun k => (htimes k).2.1)
    gE DE P.m04 hcomplete hoperator G.exhaustion.space G.exhaustion.space_open
    G.exhaustion.space_increasing G.exhaustion.space_covers G.exhaustion.space_compactClosure
    G.limit.base G.exhaustion.base_mem ψ hψsource c hcoverC hjet
    U (fun m => d (j m) / 32) (fun m => div_pos (hd (j m)) (by norm_num))
    L hmetric hlocalOperator htriple
  exact ⟨η, hη, hn, ψ, hψsource, htimes, hinverse, c, hcinverse, hcchart, hcoverC,
    hjet, Bglobal, hBglobal, hbound⟩

end PoincareConjecture.M47
