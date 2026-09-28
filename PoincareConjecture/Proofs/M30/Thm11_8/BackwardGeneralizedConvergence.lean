import PoincareConjecture.Proofs.M30.Thm11_8.HorizonTimeSequence
import PoincareConjecture.Proofs.M30.Thm11_8.GrowingTimeSourceFamily
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ExpandingReferenceSource
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ExpandingCompactness
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardRetainedFlow
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardCurvature
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardBlowupLimit
import PoincareConjecture.Proofs.M30.Thm11_8.ExhaustionTimeDomains
import PoincareConjecture.Proofs.M30.Universe.OutputSourceCylinder
import PoincareConjecture.Proofs.M30.Universe.OutputOrdinarySourceJets
import PoincareConjecture.Proofs.M30.Thm11_1.TerminalVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SourceBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Parametrized.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 2400000 in

theorem exists_backward_generalizedBlowupConvergence
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (S : GeneralizedBlowupSequence.{u})
    {T0 : ℝ≥0∞} {rho v : ℝ}
    (hT0 : 0 < T0) (hrho : 0 < rho) (hv : 0 < v)
    (hcompact : BlowupBaseBallsCompact S)
    (hcyl : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T0 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A →
        ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S k A T B eta))
    (hvolume : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S.flow k).metric (S.base k).1)
          (S.baseBall k rho)) :
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T0)) := by
  classical
  obtain ⟨Tseq, hTmono, hT, hcofinal, hcompactTime⟩ :=
    exists_strictMono_backward_time_exhaustion hT0
  have hB : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
        Nonempty (ControlledBlowupCylinder S k A (Tseq j) B eta) := by
    intro j
    exact hcyl (Tseq j) (hT j).1 (hT j).2
  choose B hBnonneg hBfamily using hB
  have hvolbar := hvolume.mono fun _ hk => scaled_terminal_volume_lower_bound hk
  obtain ⟨sigma, hsigma, E, O, hO, hOzero, hOcurv, hOdefect, hOnorm,
      hOvol, hOcompact⟩ :=
    exists_growing_time_ordinary_source_family S rho v Tseq B hrho
      (fun j => (hT j).1) hTmono.monotone hcompact
      (fun j A hA eta heta => hBfamily j A hA eta heta) hvolbar
  let W (k : ℕ) : ℝ := (k : ℝ) + rho + 2
  have hW (k : ℕ) : 0 < W k := by
    dsimp [W]
    positivity
  let C (n : ℕ) := (S.flow n).slice (S.base n).1
  let gbar (n : ℕ) : RiemannianMetric 3 (C n).carrier :=
    M13.scaleSmoothMetric ((S.flow n).metric (S.base n).1)
      (S.scale n) (S.base_scalar_pos n)
  let U (k : ℕ) : TopologicalSpace.Opens (C (sigma k)).carrier :=
    ⟨S.baseBall (sigma k) (W k), baseBall_isOpen S (sigma k) (W k)⟩
  let p (k : ℕ) : U k :=
    ⟨(S.base (sigma k)).2, (baseBall_pointed_connected S (sigma k) (hW k)).1⟩
  let : ∀ k, ConnectedSpace (U k) := fun k =>
    (baseBall_pointed_connected S (sigma k) (hW k)).2
  have hTpos (j : ℕ) : 0 < Tseq j := (hT j).1
  have hcurvRef : ∀ j k, j ≤ k → ∀ s ∈ Icc (-(Tseq j)) 0,
      ∀ x : U k, ((O k).connection s).curvatureTensorNorm x ≤ B j :=
    fun j k hjk s hs x => hOcurv j k hjk s hs x
  have hvolRef : ∀ᶠ k : ℕ in atTop, ENNReal.ofReal v ≤
      ((O k).metric 0).volumeMeasure (((O k).metric 0).ball (p k) rho) := by
    simpa only [p] using (Eventually.of_forall hOvol)
  have hcompactRef : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      IsCompact (closure (((O k).metric 0).ball (p k) A)) := by
    simpa only [p] using hOcompact
  obtain ⟨⟨htheta, htheta1, hthetaT⟩, hWopen, hWord, hwindow,
      Href, e, heBase, hFseqMetric, hWindowBounds⟩ :=
    exists_expanding_reference_source_family Tseq B hT hTmono.monotone hcofinal hrho hv
      (fun k => U k) O p hcurvRef hvolRef hcompactRef
  let theta : ℝ := min 1 (Tseq 0 / 2)
  let r : ℝ := theta / 2
  let Jshift (k : ℕ) : Set ℝ := Icc (r - Tseq k) r
  let Wtime : Set ℝ := {t : ℝ | t < r ∧ ENNReal.ofReal (r - t) < T0}
  let Fseq (k : ℕ) : RicciFlow 3 (Href.sequence.carrier k).carrier (Jshift k) :=
    ((O k).pullbackDiffeomorph (e k)).translate (-r)
      (by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      ordConnected_Icc
      (by
        refine ⟨r - Tseq k, ⟨le_rfl, ?_⟩, r, ⟨?_, le_rfl⟩, ?_⟩
        all_goals linarith [hTpos k])
  have hFseqMetric' : ∀ k, (Fseq k).metric = (Href.sequence.flow k).flow.metric := by
    simpa only [Fseq] using hFseqMetric
  have htime : ∀ a b : ℝ, Icc a b ⊆ Wtime →
      ∀ᶠ k : ℕ in atTop, Icc a b ⊆ Jshift k := by
    intro a b hab
    obtain ⟨j, _hj, htail⟩ := hWindowBounds a b hab
    filter_upwards [eventually_ge_atTop j] with k hk
    exact (htail k hk).1
  have hcurv : ∀ a b : ℝ, Icc a b ⊆ Wtime →
      ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ᶠ k : ℕ in atTop,
        ∀ t ∈ Icc a b, ∀ x : (Href.sequence.carrier k).carrier,
          ((Fseq k).connection t).curvatureTensorNorm x ≤ Cb := by
    intro a b hab
    obtain ⟨j, hj, htail⟩ := hWindowBounds a b hab
    refine ⟨B j, hj, ?_⟩
    filter_upwards [eventually_ge_atTop j] with k hk t ht x
    exact (htail k hk).2 t ht x
  obtain ⟨G, Fopen, hFopenMetric, hFopenComplete, hOpenJets⟩ :=
    exists_complete_reference_convergence_of_expanding_bounds (n := 3) (by norm_num)
      Href hShi Fseq hFseqMetric' hWopen hWord hwindow htime hcurv
  let Fsrc (k : ℕ) : RicciFlow 3 (Href.sequence.carrier k).carrier
      (Icc (-(Tseq k)) 0) := (O k).pullbackDiffeomorph (e k)
  have hmetricSrc : ∀ k t, (Fsrc k).metric t =
      (Href.sequence.flow k).flow.metric (t + r) := by
    intro k t
    have hm := congrFun (hFseqMetric' k) (t + r)
    change ((O k).pullbackDiffeomorph (e k)).metric t = _
    change ((O k).pullbackDiffeomorph (e k)).metric (t + r + -r) = _ at hm
    convert hm using 1; ring
  have hsmall (k : ℕ) : Icc (-(Tseq 0)) 0 ⊆ Icc (-(Tseq k)) 0 := by
    intro t ht
    exact ⟨(neg_le_neg (hTmono.monotone (Nat.zero_le k))).trans ht.1, ht.2⟩
  have hTbig : 0 < Tseq 0 := hTpos 0
  have hne (d : ℝ) (hd : 0 < d) : (Icc (-d) (0 : ℝ)).Nontrivial :=
    ⟨-d, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩
  let Fbig (k : ℕ) : RicciFlow 3 (Href.sequence.carrier k).carrier
      (Icc (-(Tseq 0)) 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow (Fsrc k)
      (hsmall k) ordConnected_Icc (hne (Tseq 0) hTbig)
  have hmetricBig : ∀ k t, (Fbig k).metric t =
      (Href.sequence.flow k).flow.metric (t + r) := by
    intro k t
    exact hmetricSrc k t
  have hcurvSrc (j k : ℕ) (hjk : j ≤ k) (t : ℝ)
      (ht : t ∈ Icc (-(Tseq j)) 0) (x : (Href.sequence.carrier k).carrier) :
      ((Fsrc k).connection t).curvatureTensorNorm x ≤ B j := by
    rw [RicciFlow.pullbackDiffeomorph_curvatureTensorNorm]
    exact hOcurv j k hjk t ht (e k x)
  have hcurvBig : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-(Tseq 0)) 0,
      ∀ x : (Href.sequence.carrier k).carrier,
        ((Fbig k).connection t).curvatureTensorNorm x ≤ B 0 := by
    filter_upwards [eventually_ge_atTop 0] with k _ t ht x
    exact hcurvSrc 0 k (Nat.zero_le k) t ht x
  have hnormalized (k : ℕ) :
      ((Fsrc k).connection 0).scalarCurvature (Href.sequence.flow k).base = 1 := by
    rw [RicciFlow.pullbackDiffeomorph_scalarCurvature, heBase]
    exact hOnorm k
  have hball (k : ℕ) (A : ℝ) :
      ((Fsrc k).metric 0).ball (Href.sequence.flow k).base A =
        (e k) ⁻¹' (((O k).metric 0).ball (p k) A) := by
    ext x
    change ((Fsrc k).metric 0).edist (Href.sequence.flow k).base x < ENNReal.ofReal A ↔ _
    rw [RicciFlow.pullbackDiffeomorph_edist, heBase]
    rfl
  have hcompactBig (A : ℝ) (hA : 0 < A) : ∀ᶠ k : ℕ in atTop,
      IsCompact (closure (((Fbig k).metric 0).ball (Href.sequence.flow k).base A)) := by
    filter_upwards [hOcompact A hA] with k hk
    change IsCompact (closure (((Fsrc k).metric 0).ball (Href.sequence.flow k).base A))
    rw [hball]
    change IsCompact (closure ((e k).toHomeomorph ⁻¹' (((O k).metric 0).ball (p k) A)))
    rw [← (e k).toHomeomorph.preimage_closure]
    exact (e k).toHomeomorph.isCompact_preimage.mpr hk
  have hzero : (0 : ℝ) ∈ Ioo (-theta / 2) (theta / 2) := by
    constructor <;> dsimp [theta, r] <;> linarith [htheta]
  have hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) := by
    change G.limitCarrier.metricComplete (G.limitFlow.flow.metric 0)
    rw [← hFopenMetric]
    exact hFopenComplete
  have hrT0 : ENNReal.ofReal r < T0 := by
    exact (ENNReal.ofReal_le_ofReal (by dsimp [r]; linarith [hthetaT])).trans_lt (hT 0).2
  have hOpenJets' : ∀ (q : G.limitCarrier.carrier) (m : ℕ)
      (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))), IsCompact K →
      K ⊆ {s : ℝ | s < theta / 2 ∧ ENNReal.ofReal (theta / 2 - s) < T0} ×ˢ
        (extChartAt (𝓡 3) q).target →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
            ((Href.sequence.flow (G.subsequence k)).flow.metric z.1).pullbackCoefficients
              ((fun y => ((G.embedding k).toFun (0, y)).2) ∘
                (extChartAt (𝓡 3) q).symm) z.2))
        (iteratedFDeriv ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
            (Fopen.metric z.1).pullbackCoefficients
              (extChartAt (𝓡 3) q).symm z.2)) atTop K := by
    intro q m K hK hKJ
    have h := hOpenJets q m K hK hKJ
    simpa only [hFseqMetric'] using h
  obtain ⟨F, hFpast, hFjets⟩ := exists_backward_flow_on_retained_carrier
    hShi hMixed hFlow (T := theta) (Tbig := Tseq 0) (tau := r) (B := B 0)
    (T0 := T0) (by dsimp [r]; linarith [htheta])
    (by dsimp [r]; linarith [htheta]) htheta1 hthetaT hrT0
    G hcomplete Fopen hFopenMetric hOpenJets' Fbig hmetricBig hcurvBig hcompactBig
  have htimeFull : ∀ A : ℝ, 0 < A → ENNReal.ofReal A < T0 →
      ∀ᶠ k : ℕ in atTop, Icc (-A) 0 ⊆ Icc (-(Tseq k)) 0 := by
    intro A hA hAT
    exact hcofinal (-(-A)) (by simpa only [neg_neg] using hAT) |>.mono
      (fun k hk t ht => ⟨by linarith [hk, ht.1], ht.2⟩)
  have hnegative (k : ℕ) (t : ℝ) (ht : t ∈ Icc (-(Tseq k)) 0)
      (x : (Href.sequence.carrier k).carrier) :
      ((Fsrc k).connection t).negativeCurvaturePart x ≤
        1 / ((k : ℝ) + 1) := by
    let Jk : SpacetimeInterval := {
      domain := Icc (-(Tseq k)) 0
      ordConnected := ordConnected_Icc
      nontrivial := hne (Tseq k) (hTpos k) }
    have hid := MetricSurgery.negativeCurvaturePart_eq_of_local_isometry
      ((Fsrc k).connection t) ((O k).connection t) isOpen_univ
      (e k).contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)
    rw [hid, Cylinder.negativeCurvaturePart_of_ordinaryFlow
      (J := Jk) (E k).embedding (O k) (hO k) t ht (e k x)]
    apply (div_le_iff₀ (S.base_scalar_pos (sigma k))).mpr
    exact (E k).negative_curvature_bound t ht (e k x).val (e k x).property
  let psi (k : ℕ) (x : G.limitCarrier.carrier) :=
    ((G.embedding k).toFun (0, x)).2
  have hdefect (t : ℝ) (ht : t ∈ blowupBackwardInterval T0)
      (x : G.limitCarrier.carrier) :
      Tendsto (fun k => ((Fsrc (G.subsequence k)).connection t).negativeCurvaturePart
        (psi k x)) atTop (𝓝 0) := by
    have hmem : ∀ᶠ k : ℕ in atTop,
        t ∈ Icc (-(Tseq (G.subsequence k))) 0 := by
      have hc := hcompactTime ({t} : Set ℝ) isCompact_singleton
        (singleton_subset_iff.mpr ht)
      filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hc] with k hk
      exact hk (mem_singleton t)
    apply squeeze_zero' (Eventually.of_forall (fun k => le_max_right _ _))
      (hmem.mono fun k hk => hnegative (G.subsequence k) t hk (psi k x))
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp
      G.subsequence_strictMono.tendsto_atTop
  have hreadout := tendsto_backward_curvature hSlice
    ⟨by linarith [htheta], by linarith [htheta]⟩
    G Fsrc htimeFull F hFjets hdefect
  have hcurvLimit : ∀ A : ℝ, 0 < A → ENNReal.ofReal A < T0 →
      ∃ K : ℝ, ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-A) 0,
        ∀ x : (Href.sequence.carrier k).carrier,
          ((Fsrc k).connection t).curvatureTensorNorm x ≤ K := by
    intro A hA hAT
    obtain ⟨j, hj⟩ := (hcofinal A hAT).exists
    refine ⟨B j, ?_⟩
    filter_upwards [eventually_ge_atTop j] with k hk t ht x
    have hAj : A ≤ Tseq j := hj.le
    exact hcurvSrc j k hk t (⟨(neg_le_neg hAj).trans ht.1, ht.2⟩) x
  have hrpos : 0 < r := by dsimp [r]; linarith [htheta]
  have hrefmem : (-r : ℝ) ∈ blowupBackwardInterval T0 := by
    refine ⟨neg_nonpos.mpr hrpos.le, ?_⟩
    have hrle : r ≤ Tseq 0 := by dsimp [r]; linarith [hthetaT]
    simpa only [neg_neg] using (ENNReal.ofReal_le_ofReal hrle).trans_lt (hT 0).2
  let L0 : BlowupLimitFlow.{0} (blowupBackwardInterval T0) :=
    retainedBackwardBlowupLimit G Fsrc F (by linarith [hrpos]) hrefmem
      (by
        have heq := hFpast (show (-r : ℝ) ∈ {t : ℝ | t < 0 ∧
          ENNReal.ofReal (-t) < T0} by
          refine ⟨by linarith [hrpos], ?_⟩
          have hrle : r ≤ Tseq 0 := by dsimp [r]; linarith [hthetaT]
          simpa only [neg_neg] using (ENNReal.ofReal_le_ofReal hrle).trans_lt (hT 0).2)
        rw [heq]
        convert hFopenComplete using 1; dsimp [r]; ring)
      hcurvLimit (Eventually.of_forall hnormalized) hreadout
  let L := liftBlowupLimit.{u} L0
  let a (k : ℕ) : G.limitCarrier.carrier → U (G.subsequence k) :=
    e (G.subsequence k) ∘ psi k
  have hpsi (k : ℕ) : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (psi k) (G.exhaustion k) :=
    Poincare.isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv (G.exhaustion_open k)
      (fun x hx => ((G.embedding k).spatialMap_contMDiffAt
        (G.exhaustion_open k) hzero hx).contMDiffWithinAt)
      (fun x hx => (G.embedding k).spatialMap_mfderiv_bijective
        (G.exhaustion_open k) hzero hx)
  have ha (k : ℕ) : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (a k) (G.exhaustion k) := by
    intro x
    exact (hpsi k x).comp (𝓡 3) (U (G.subsequence k))
      ((e (G.subsequence k)).isLocalDiffeomorph (psi k x.val))
  have hemb (k : ℕ) : Topology.IsOpenEmbedding
      (fun x : G.exhaustion k => a k x.val) :=
    (e (G.subsequence k)).toHomeomorph.isOpenEmbedding.comp
      ((G.embedding k).spatialHomeomorph (G.exhaustion_open k) hzero).isOpenEmbedding_restrict
  let out (k : ℕ) := liftCylinderOfOrdinaryEmbedding L0 (U (G.subsequence k))
    (E (G.subsequence k)).embedding (G.exhaustion k) (G.exhaustion_open k)
    (a k) (hemb k) (ha k)
  let home : L.carrier.carrier ≃ₜ G.limitCarrier.carrier := Homeomorph.ulift
  let X : BlowupExhaustion L := {
    space := fun k => home ⁻¹' G.exhaustion k
    space_open := fun k => (G.exhaustion_open k).preimage home.continuous
    space_connected := fun k => home.isConnected_preimage.mpr (G.exhaustion_connected k)
    space_compactClosure := by
      intro k
      rw [← home.preimage_closure]
      exact home.isCompact_preimage.mpr (G.exhaustion_compactClosure k)
    space_increasing := fun _ _ hij _ hx => G.exhaustion_monotone hij hx
    space_covers := by
      apply subset_antisymm (subset_univ _)
      intro x _
      have hx : home x ∈ ⋃ k, G.exhaustion k := by rw [G.exhaustion_covers]; trivial
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨k, hk⟩
    base_mem := G.base_in_exhaustion
    time := fun k => Tseq (G.subsequence k)
    time_pos := fun k => hTpos _
    time_increasing := fun i j hij => hTmono.monotone
      (G.subsequence_strictMono.monotone hij)
    time_subset := fun k t ht =>
      ⟨ht.2, by
        have hT' : ENNReal.ofReal (- -Tseq (G.subsequence k)) < T0 := by
          simpa only [neg_neg] using (hT (G.subsequence k)).2
        exact (ENNReal.ofReal_le_ofReal (neg_le_neg ht.1)).trans_lt hT'⟩
    time_cofinal := fun I hI hIJ =>
      (G.subsequence_strictMono.tendsto_atTop.eventually (hcompactTime I hI hIJ)).mono
        (fun k hk => hk) }
  have hbase (k : ℕ) : a k G.limitFlow.base = p (G.subsequence k) := by
    have hb := congrArg Prod.snd (G.base_preserving k)
    change psi k G.limitFlow.base = (Href.sequence.flow (G.subsequence k)).base at hb
    dsimp only [a, Function.comp_apply]
    rw [hb, heBase]
  refine ⟨{
    limit := L
    subsequence := sigma ∘ G.subsequence
    subsequence_strictMono := hsigma.comp G.subsequence_strictMono
    exhaustion := X
    embedding := out
    base_preserving := ?_
    source_balls_in_image := ?_
    pullback_metric_CInfinity := ?_ }⟩
  · intro k h0
    change (E (G.subsequence k)).embedding.pointMap 0 _ (a k G.limitFlow.base).val = _
    rw [hbase]
    exact (E (G.subsequence k)).zero_identity _ (p (G.subsequence k)).val
      (p (G.subsequence k)).property
  · intro A hA
    let Cb : ℝ := (3 : ℝ) ^ 3 * max (B 0) 1
    let R : ℝ := Real.exp (Cb * Tseq 0) * A
    have hCb : 0 ≤ Cb := mul_nonneg (by positivity)
      (zero_le_one.trans (le_max_right (B 0) 1))
    have hR : 0 < R := mul_pos (Real.exp_pos _) hA
    have hRic (i : ℕ) (t : ℝ) (ht : t ∈ Icc (-(Tseq 0)) 0)
        (x : (Href.sequence.carrier i).carrier) (w : TangentSpace (𝓡 3) x) :
        |((Fsrc i).connection t).ricci x w w| ≤
          Cb * ((Fsrc i).metric t).inner x w w := by
      have hQ : 0 ≤ ((Fsrc i).metric t).inner x w w := by
        by_cases hw : w = 0
        · subst w; simp
        · exact (((Fsrc i).metric t).pos x w hw).le
      have hnorm := ((Fsrc i).connection t).abs_ricci_quadratic_le_curvatureTensorNorm x w
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := finrank_euclideanSpace_fin
      simp only [Fintype.card_fin, hdim] at hnorm
      exact hnorm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((hcurvSrc 0 i (Nat.zero_le i) t ht x).trans
          (le_max_left (B 0) 1)) (by positivity)) hQ)
    have hgrowth : ∀ᶠ k : ℕ in atTop, A < W (G.subsequence k) := by
      obtain ⟨N, hN⟩ := exists_nat_ge A
      filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually
        (eventually_ge_atTop N)] with k hk
      have hNk : (N : ℝ) ≤ (G.subsequence k : ℝ) := by exact_mod_cast hk
      dsimp [W]
      linarith
    have hcover := G.eventually_source_ball_subset_image_ball hzero hzero hcomplete
      hR (show (1 : ℝ) < 2 by norm_num)
    have hclosed : IsCompact (closure ((G.limitFlow.metricAt 0).ball
        G.limitFlow.base (2 * R))) :=
      (G.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hcomplete
        G.limitFlow.base (2 * R)
    obtain ⟨N, hN⟩ := G.exists_exhaustion_superset hclosed
    filter_upwards [hgrowth, hcover, eventually_ge_atTop N] with k hk hcover hkN x hx
    have hcontained : (gbar (sigma (G.subsequence k))).ball
        (S.base (sigma (G.subsequence k))).2 A ⊆ U (G.subsequence k) := by
      intro y hy
      change y ∈ S.baseBall (sigma (G.subsequence k)) (W (G.subsequence k))
      rw [← scaled_terminal_ball_eq_baseBall]
      exact hy.trans_le (ENNReal.ofReal_le_ofReal hk.le)
    have hxbar : x ∈ (gbar (sigma (G.subsequence k))).ball
        (S.base (sigma (G.subsequence k))).2 A := by
      rwa [scaled_terminal_ball_eq_baseBall]
    let xu : U (G.subsequence k) := ⟨x, hcontained hxbar⟩
    have hxu : xu ∈
        ((O (G.subsequence k)).metric 0).ball (p (G.subsequence k)) A := by
      rw [intrinsic_ball_eq_preimage (gbar (sigma (G.subsequence k)))
        (U (G.subsequence k)) ((O (G.subsequence k)).metric 0)
        (hOzero (G.subsequence k)) (p (G.subsequence k)) hcontained]
      exact hxbar
    let z := (e (G.subsequence k)).symm xu
    have hz : z ∈ ((Fsrc (G.subsequence k)).metric 0).ball
        (Href.sequence.flow (G.subsequence k)).base A := by
      rw [hball]
      change e (G.subsequence k) ((e (G.subsequence k)).symm xu) ∈
        ((O (G.subsequence k)).metric 0).ball (p (G.subsequence k)) A
      rw [Diffeomorph.apply_symm_apply]
      exact hxu
    have hzeroBig : (0 : ℝ) ∈ Icc (-(Tseq 0)) 0 :=
      ⟨by linarith [hTpos 0], le_rfl⟩
    have hrle0 : r ≤ Tseq 0 := by dsimp [r]; linarith [hthetaT]
    have hrlek : r ≤ Tseq (G.subsequence k) :=
      hrle0.trans (hTmono.monotone (Nat.zero_le (G.subsequence k)))
    have hrefBig : -r ∈ Icc (-(Tseq 0)) 0 := by
      exact ⟨neg_le_neg hrle0, by linarith [hrpos]⟩
    have hcmp := (Fsrc (G.subsequence k)).ball_subset_ball_of_ricci_bound
      (convex_Icc (-(Tseq 0)) 0) (hsmall (G.subsequence k))
      (Href.sequence.flow (G.subsequence k)).base A Cb hzeroBig hrefBig
      (fun t ht y _ w => hRic (G.subsequence k) t ht y w)
    have hdisplacement : |(-r) - (0 : ℝ)| ≤ Tseq 0 := by
      rw [sub_zero, abs_of_neg (by linarith [hrpos])]
      simpa only [neg_neg] using hrle0
    have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdisplacement hCb)
    have hzRef : z ∈ ((Fsrc (G.subsequence k)).metric (-r)).ball
        (Href.sequence.flow (G.subsequence k)).base R :=
      by
        change ((Fsrc (G.subsequence k)).metric (-r)).edist
          (Href.sequence.flow (G.subsequence k)).base z < ENNReal.ofReal R
        simpa only [R, ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
          using (hcmp hz).trans_le (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right hexp hA.le))
    have href : (Fsrc (G.subsequence k)).metric (-r) =
        (Href.sequence.flow (G.subsequence k)).flow.metric 0 := by
      rw [hmetricSrc]
      congr 1
      ring
    rw [href] at hzRef
    obtain ⟨y, hy, hpy⟩ := hcover hzRef
    have hay : a k y = xu := by
      change e (G.subsequence k) (psi k y) = xu
      change psi k y = z at hpy
      rw [hpy]
      exact (e (G.subsequence k)).apply_symm_apply xu
    refine ⟨ULift.up y, G.exhaustion_monotone hkN (hN (subset_closure hy)),
      ⟨by linarith [hTpos (G.subsequence k)], le_rfl⟩, ?_⟩
    change (E (G.subsequence k)).embedding.pointMap 0 _ (a k y).val = _
    rw [hay]
    exact (E (G.subsequence k)).zero_identity _ xu.val xu.property
  · dsimp only
    intro q j r K hK hKstage eps heps
    rcases q with ⟨q⟩
    let V := EuclideanSpace ℝ (Fin 3)
    let : NormedAddCommGroup (V →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
    let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
    let Z := ℝ × V
    let Bilin := V →L[ℝ] V →L[ℝ] ℝ
    let c := extChartAt (𝓡 3) q
    let Q := blowupBackwardInterval T0 ×ˢ c.target
    let f : ℕ → Z → Bilin := fun k z =>
      ((Fsrc (G.subsequence k)).metric z.1).pullbackCoefficients
        (psi k ∘ c.symm) z.2
    let g : Z → Bilin := fun z =>
      (F.metric z.1).pullbackCoefficients c.symm z.2
    have hKQ : K ⊆ Q := by
      intro z hz
      have ht := (hKstage hz).1
      change z ∈ blowupMetricChartDomain (liftBlowupLimit.{u} L0) (ULift.up q) at ht
      rw [liftBlowupLimit_metricChartDomain] at ht
      exact ht
    have hstage (z : Z) (hz : z ∈ K) : c.symm z.2 ∈ G.exhaustion j :=
      (hKstage hz).2
    let I : Set ℝ := {t : ℝ | ENNReal.ofReal (-t) < T0}
    have hI : IsOpen I :=
      isOpen_Iio.preimage (ENNReal.continuous_ofReal.comp continuous_neg)
    have hJ : blowupBackwardInterval T0 = I ∩ Iic 0 := by
      ext t
      exact and_comm
    have htimeUnique : UniqueDiffOn ℝ (blowupBackwardInterval T0) := by
      rw [hJ]
      simpa only [inter_comm] using (uniqueDiffOn_Iic (0 : ℝ)).inter hI
    have hQ : UniqueDiffOn ℝ Q :=
      htimeUnique.prod (isOpen_extChartAt_target (I := 𝓡 3) q).uniqueDiffOn
    have hchart (y : V) (hy : y ∈ c.target) :
        ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
      (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy).contMDiffAt
        (extChartAt_target_mem_nhds' hy)
    have hKtime : Prod.fst '' K ⊆ blowupBackwardInterval T0 := by
      rintro t ⟨z, hz, rfl⟩
      exact (hKQ hz).1
    have hKtimeCompact : IsCompact (Prod.fst '' K) :=
      hK.image continuous_fst
    have htimeTail : ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
        z.1 ∈ Icc (-(Tseq (G.subsequence k))) 0 := by
      have htail := hcompactTime (Prod.fst '' K) hKtimeCompact hKtime
      filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually htail] with k hk z hz
      exact hk (mem_image_of_mem Prod.fst hz)
    have htimeTailStrict : ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
        z.1 ∈ Ioi (-(Tseq (G.subsequence k))) := by
      by_cases hKne : K.Nonempty
      · have hKtimeNe : (Prod.fst '' K).Nonempty := hKne.image Prod.fst
        obtain ⟨a₀, ha₀, ha⟩ := hKtimeCompact.exists_isLeast hKtimeNe
        have haT : ENNReal.ofReal (-a₀) < T0 := (hKtime ha₀).2
        filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually
          (hcofinal (-a₀) haT)] with k hk z hz
        have hza : a₀ ≤ z.1 := ha (mem_image_of_mem Prod.fst hz)
        have hneg : -Tseq (G.subsequence k) < a₀ := by linarith
        exact hneg.trans_le hza
      · exact Eventually.of_forall (fun _ z hz => False.elim (hKne ⟨z, hz⟩))
    have hsource : ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
        ContDiffWithinAt ℝ ∞ (f k) Q z := by
      filter_upwards [htimeTailStrict, eventually_ge_atTop j] with k htk hj z hz
      have hzt : z.1 ∈ Icc (-(Tseq (G.subsequence k))) 0 :=
        ⟨(htk z hz).le, (hKQ hz).1.1⟩
      have hmap := (G.embedding k).spatialMap_contMDiffAt
        (G.exhaustion_open k) hzero
        (G.exhaustion_monotone hj (hstage z hz))
      have hlocal :=
        ((Fsrc (G.subsequence k)).smooth.contDiffWithinAt_spacetime_pullbackCoefficients
          (hmap.comp z.2 (hchart z.2 (hKQ hz).2)) hzt)
      have hstrict :
          Ioo (-(Tseq (G.subsequence k))) 1 ×ˢ (Set.univ : Set V) ∈ 𝓝 z := by
        apply IsOpen.mem_nhds
        · exact isOpen_Ioo.prod isOpen_univ
        · exact ⟨⟨htk z hz, by linarith [(hKQ hz).1.1]⟩, mem_univ _⟩
      have hsourceSet :
          Icc (-(Tseq (G.subsequence k))) 0 ×ˢ (Set.univ : Set V) ∈ 𝓝[Q] z := by
        apply Filter.mem_of_superset
          (inter_mem (mem_nhdsWithin_of_mem_nhds hstrict) self_mem_nhdsWithin)
        intro y hy
        exact ⟨⟨le_of_lt hy.1.1.1, hy.2.1.1⟩, mem_univ _⟩
      exact hlocal.mono_of_mem_nhdsWithin hsourceSet
    have hlimit (z : Z) (hz : z ∈ K) :
        ContDiffWithinAt ℝ ∞ g Q z :=
      (F.smooth.contDiffWithinAt_spacetime_pullbackCoefficients
        (hchart z.2 (hKQ hz).2) (hKQ hz).1).mono
          (prod_mono subset_rfl (subset_univ _))
    have hscalar (aa bb : Fin 3) : TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ r
          (fun z => f k z (EuclideanSpace.basisFun (Fin 3) ℝ aa)
            (EuclideanSpace.basisFun (Fin 3) ℝ bb)) Q)
        (iteratedFDerivWithin ℝ r
          (L0.carrier.coordinateCoefficient q
            (fun t x v w => (L0.flow.metric t).inner x v w) aa bb) Q) atTop K := by
      let Eval : Bilin →L[ℝ] ℝ :=
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ bb)).comp
          (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ)
            (EuclideanSpace.basisFun (Fin 3) ℝ aa))
      let Evalr := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin r => Z) Bilin ℝ Eval
      have hbilinear : TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ r (f k) Q)
          (iteratedFDerivWithin ℝ r g Q) atTop K := by
        simpa [f, psi, Fbig, c, Q, g,
          Poincare.Geometry.RicciFlow.Harnack.restrictFlow] using hFjets q r K hK hKQ
      have heval := Evalr.uniformContinuous.comp_tendstoUniformlyOn hbilinear
      change TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ r (Eval ∘ f k) Q)
        (iteratedFDerivWithin ℝ r (Eval ∘ g) Q) atTop K
      have hr : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
        WithTop.coe_le_coe.mpr (le_top : (r : ℕ∞) ≤ ⊤)
      refine (heval.congr ?_).congr_right ?_
      · filter_upwards [hsource] with k hk z hz
        exact (Eval.iteratedFDerivWithin_comp_left (hk z hz) hQ (hKQ hz) hr).symm
      · intro z hz
        exact (Eval.iteratedFDerivWithin_comp_left (hlimit z hz) hQ (hKQ hz) hr).symm
    have htail : ∀ᶠ k : ℕ in atTop, ∀ aa bb : Fin 3, ∀ z ∈ K,
        ‖iteratedFDerivWithin ℝ r
            (fun z => f k z (EuclideanSpace.basisFun (Fin 3) ℝ aa)
              (EuclideanSpace.basisFun (Fin 3) ℝ bb)) Q z -
          iteratedFDerivWithin ℝ r
            (L0.carrier.coordinateCoefficient q
              (fun t x v w => (L0.flow.metric t).inner x v w) aa bb) Q z‖ < eps := by
      apply eventually_all.mpr
      intro aa
      apply eventually_all.mpr
      intro bb
      filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hscalar aa bb)) eps heps] with k hk z hz
      have hdist := hk z hz
      rw [dist_comm, dist_eq_norm] at hdist
      exact hdist
    obtain ⟨N, hN⟩ := eventually_atTop.mp htail
    obtain ⟨Nt, hNt⟩ := eventually_atTop.mp htimeTail
    obtain ⟨Ns, hNs⟩ := eventually_atTop.mp htimeTailStrict
    refine ⟨max (max (max j N) Nt) Ns,
      (le_max_left j N).trans
        ((le_max_left (max j N) Nt).trans (le_max_left (max (max j N) Nt) Ns)), ?_⟩
    intro k hk
    have houter : max (max j N) Nt ≤ k := (le_max_left _ _).trans hk
    have hbaseMax : max j N ≤ k := (le_max_left _ _).trans houter
    have hjk : j ≤ k := (le_max_left _ _).trans hbaseMax
    have hNk : N ≤ k := (le_max_right _ _).trans hbaseMax
    have hNtk : Nt ≤ k := (le_max_right _ _).trans houter
    have hNsk : Ns ≤ k := (le_max_right _ _).trans hk
    refine ⟨?_, ?_⟩
    · intro z hz
      have hdom : z ∈ blowupMetricChartDomain (liftBlowupLimit.{u} L0) (ULift.up q) := by
        rw [liftBlowupLimit_metricChartDomain]
        exact hKQ hz
      exact ⟨hNt k hNtk z hz, hdom.2⟩
    · intro aa bb z hz
      have hxs : c.symm z.2 ∈ G.exhaustion k :=
        G.exhaustion_monotone hjk (hstage z hz)
      have hsourceTime : z.1 ∈ Icc (-(Tseq (G.subsequence k))) 0 :=
        hNt k hNtk z hz
      have hsourceJet := liftCylinder_iteratedFDerivWithin_ordinaryCoefficient
        L0 (U (G.subsequence k)) (E (G.subsequence k)).embedding
        (O (G.subsequence k))
        (fun t ht x v w => hO (G.subsequence k) t ht x v w)
        (G.exhaustion_open k) (a k) (ha k).contMDiffOn (out k)
        (fun _ _ _ => rfl) q aa bb r z
        ⟨hsourceTime, (hKQ hz).2⟩ hxs
      have htargetJet := liftBlowupLimit_iteratedFDerivWithin_coordinateCoefficient.{u}
        L0 q aa bb r z (hKQ hz)
      have hcoeff :
          (fun y : Z => f k y (EuclideanSpace.basisFun (Fin 3) ℝ aa)
            (EuclideanSpace.basisFun (Fin 3) ℝ bb)) =
          (fun y : Z => ((O (G.subsequence k)).metric y.1).pullbackCoefficients
            (a k ∘ c.symm) y.2 (EuclideanSpace.basisFun (Fin 3) ℝ aa)
              (EuclideanSpace.basisFun (Fin 3) ℝ bb)) := by
        funext y
        have hc := ((O (G.subsequence k)).metric y.1).parametrizedCoefficients_pullbackOfDiffeomorph
          (e (G.subsequence k)) (psi k ∘ c.symm)
        rw [RiemannianMetric.parametrizedCoefficients_eq_pullbackCoefficients,
          RiemannianMetric.parametrizedCoefficients_eq_pullbackCoefficients] at hc
        exact congrArg (fun b => b y.2 (EuclideanSpace.basisFun (Fin 3) ℝ aa)
          (EuclideanSpace.basisFun (Fin 3) ℝ bb)) hc
      have hset :
          Icc (-(Tseq (G.subsequence k))) 0 ×ˢ c.target =ᶠ[𝓝 z] Q := by
        have hopen : IsOpen
            (Ioo (-(Tseq (G.subsequence k))) 1 ×ˢ (Set.univ : Set V)) :=
          isOpen_Ioo.prod isOpen_univ
        have hzopen : z ∈ Ioo (-(Tseq (G.subsequence k))) 1 ×ˢ
            (Set.univ : Set V) := by
          exact ⟨⟨hNs k hNsk z hz, by linarith [(hKQ hz).1.1]⟩, mem_univ _⟩
        filter_upwards [hopen.mem_nhds hzopen] with y hy
        apply propext
        constructor
        · intro hyC
          have hyneg : -y.1 ≤ Tseq (G.subsequence k) := by
            linarith [hyC.1.1]
          have hyT : ENNReal.ofReal (-y.1) < T0 :=
            (ENNReal.ofReal_le_ofReal hyneg).trans_lt (hT (G.subsequence k)).2
          exact ⟨⟨hyC.1.2, hyT⟩, hyC.2⟩
        · intro hyQ
          exact ⟨⟨le_of_lt hy.1.1, hyQ.1.1⟩, hyQ.2⟩
      rw [hsourceJet, htargetJet, ← hcoeff]
      rw [iteratedFDerivWithin_congr_set hset r]
      exact hN k hNk aa bb z hz

end PoincareConjecture.M30
