import PoincareConjecture.Proofs.M30.Thm11_8.GrowingSourceFamily
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.PointedCompactnessInput
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.FiniteSourcePullback
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.FiniteAnalyticAssembly
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.RetainedClosedCurvature
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteBlowupLimit
import PoincareConjecture.Proofs.M30.Universe.OutputSourceCylinder
import PoincareConjecture.Proofs.M30.Universe.OutputOrdinarySourceJets
import PoincareConjecture.Proofs.M30.Generalized.OrdinaryNegativeDefect
import PoincareConjecture.Proofs.M30.Generalized.Restriction
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

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 2400000 in

theorem exists_finite_generalizedBlowupConvergence
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    (hM07 : ∀ {a b : ℝ} (H : PointedRicciFlowCompactnessHypotheses 3 a b),
      Nonempty (PointedRicciFlowCompactnessConclusion H))
    (S : GeneralizedBlowupSequence.{u})
    {tau T Tbig B rho v : ℝ}
    (htau : 0 < tau) (htauT : tau < T) (hT1 : T ≤ 1)
    (hTT : T < Tbig) (hrho : 0 < rho) (hv : 0 < v)
    (hcompact : BlowupBaseBallsCompact S)
    (hcyl : ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
      Nonempty (ControlledBlowupCylinder S k A Tbig B eta))
    (hvolume : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S.flow k).metric (S.base k).1)
          (S.baseBall k rho)) :
    Nonempty (GeneralizedBlowupConvergence S (Icc (-tau) 0)) := by
  classical
  have hT : 0 < T := htau.trans htauT
  have hTbig : 0 < Tbig := hT.trans hTT
  have hsmall : Icc (-T) (0 : ℝ) ⊆ Icc (-Tbig) 0 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have htauBig : Icc (-tau) (0 : ℝ) ⊆ Icc (-Tbig) 0 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hne (d : ℝ) (hd : 0 < d) : (Icc (-d) (0 : ℝ)).Nontrivial :=
    ⟨-d, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩
  have hvolbar := hvolume.mono fun _ hk => scaled_terminal_volume_lower_bound hk
  obtain ⟨sigma, hsigma, E, O, hO, hOzero, hOcurv, hOnorm, hOvol, hOcompact⟩ :=
    exists_growing_ordinary_source_family S rho v Tbig B hrho hTbig hcompact hcyl hvolbar
  let W (k : ℕ) : ℝ := (k : ℝ) + rho + 2
  let D (k : ℕ) := (S.flow (sigma k)).slice (S.base (sigma k)).1
  let U (k : ℕ) : TopologicalSpace.Opens (D k).carrier :=
    ⟨S.baseBall (sigma k) (W k), baseBall_isOpen S (sigma k) (W k)⟩
  have hW (k : ℕ) : 0 < W k := by dsimp [W]; positivity
  let p (k : ℕ) : U k :=
    ⟨(S.base (sigma k)).2, (baseBall_pointed_connected S (sigma k) (hW k)).1⟩
  let gbar (k : ℕ) : RiemannianMetric 3 (D k).carrier :=
    M13.scaleSmoothMetric ((S.flow (sigma k)).metric (S.base (sigma k)).1)
      (S.scale (sigma k)) (S.base_scalar_pos (sigma k))
  let : ∀ k, ConnectedSpace (U k) := fun k =>
    (baseBall_pointed_connected S (sigma k) (hW k)).2
  let Osmall (k : ℕ) : RicciFlow 3 (U k) (Icc (-T) 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow (O k) hsmall ordConnected_Icc (hne T hT)
  obtain ⟨H, hH⟩ := exists_pointedCompactnessHypotheses_of_finite_source_family
    hT hrho hv (fun k => U k) Osmall p
    (fun k t ht x => hOcurv k t (hsmall ht) x)
    (Eventually.of_forall hOvol) hOcompact
  choose e heBase heMetric using hH
  let Fbig (k : ℕ) : RicciFlow 3 (H.sequence.carrier k).carrier (Icc (-Tbig) 0) :=
    (O k).pullbackDiffeomorph (e k)
  have hmetric : ∀ k t, (Fbig k).metric t =
      (H.sequence.flow k).flow.metric (t + T / 2) :=
    pullback_source_metric_eq_shifted_pointed_metric H.sequence Osmall e heMetric
  have hcurv (k : ℕ) (t : ℝ) (ht : t ∈ Icc (-Tbig) 0)
      (x : (H.sequence.carrier k).carrier) :
      ((Fbig k).connection t).curvatureTensorNorm x ≤ B := by
    rw [RicciFlow.pullbackDiffeomorph_curvatureTensorNorm]
    exact hOcurv k t ht (e k x)
  have hnormalized (k : ℕ) :
      ((Fbig k).connection 0).scalarCurvature (H.sequence.flow k).base = 1 := by
    rw [RicciFlow.pullbackDiffeomorph_scalarCurvature, heBase]
    exact hOnorm k
  have hball (k : ℕ) (A : ℝ) :
      ((Fbig k).metric 0).ball (H.sequence.flow k).base A =
        (e k) ⁻¹' (((O k).metric 0).ball (p k) A) := by
    ext x
    change ((Fbig k).metric 0).edist (H.sequence.flow k).base x < ENNReal.ofReal A ↔ _
    rw [RicciFlow.pullbackDiffeomorph_edist, heBase]
    rfl
  have hcompactSmall (A : ℝ) (hA : 0 < A) : ∀ᶠ k : ℕ in atTop,
      IsCompact (closure (((Fbig k).metric 0).ball (H.sequence.flow k).base A)) := by
    filter_upwards [hOcompact A hA] with k hk
    rw [hball]
    change IsCompact (closure ((e k).toHomeomorph ⁻¹' (((O k).metric 0).ball (p k) A)))
    rw [← (e k).toHomeomorph.preimage_closure]
    exact (e k).toHomeomorph.isCompact_preimage.mpr hk
  obtain ⟨HC⟩ := hM07 H
  let G := HC.geometric_limit
  have hzero : (0 : ℝ) ∈ Ioo (-T / 2) (T / 2) := ⟨by linarith, by linarith⟩
  have hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) :=
    HC.complete_interior 0 hzero
  obtain ⟨F, hpast, hjets⟩ := exists_finite_terminal_extension_of_big_window_bounds
    hShi hMixed hFlow htau htauT hT1 hTT G hcomplete Fbig hmetric
    (Eventually.of_forall hcurv) hcompactSmall
  let psi (k : ℕ) (x : G.limitCarrier.carrier) := ((G.embedding k).toFun (0, x)).2
  let Jbig : SpacetimeInterval := {
    domain := Icc (-Tbig) 0
    ordConnected := ordConnected_Icc
    nontrivial := hne Tbig hTbig }
  have hnegative (k : ℕ) (t : ℝ) (ht : t ∈ Icc (-Tbig) 0)
      (x : (H.sequence.carrier k).carrier) :
      ((Fbig k).connection t).negativeCurvaturePart x ≤ 1 / ((k : ℝ) + 1) := by
    have hid := MetricSurgery.negativeCurvaturePart_eq_of_local_isometry
      ((Fbig k).connection t) ((O k).connection t) isOpen_univ
      (e k).contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)
    rw [hid, Cylinder.negativeCurvaturePart_of_ordinaryFlow
      (J := Jbig) (E k).embedding (O k) (hO k) t ht (e k x)]
    apply (div_le_iff₀ (S.base_scalar_pos (sigma k))).mpr
    exact (E k).negative_curvature_bound t ht (e k x).val (e k x).property
  let Fsrc (k : ℕ) : RicciFlow 3 (H.sequence.carrier k).carrier (Icc (-T) 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow (Fbig k)
      hsmall ordConnected_Icc (hne T hT)
  have hdefect (t : ℝ) (ht : t ∈ Icc (-tau) 0) (x : G.limitCarrier.carrier) :
      Tendsto (fun k => ((Fsrc (G.subsequence k)).connection t).negativeCurvaturePart
        (psi k x)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => le_max_right _ _)
      (fun k => hnegative (G.subsequence k) t (htauBig ht) (psi k x))
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp G.subsequence_strictMono.tendsto_atTop
  have hreadout := tendsto_retained_closed_curvature hSlice htau htauT G Fsrc F hjets hdefect
  let L0 : BlowupLimitFlow.{0} (Icc (-tau) 0) :=
    retainedClosedBlowupLimit htau htauT G Fsrc F hpast HC.complete_interior
      (Eventually.of_forall fun k t ht x => hcurv k t (htauBig ht) x)
      (Eventually.of_forall hnormalized) hreadout
  let L := liftBlowupLimit.{u} L0
  let a (k : ℕ) : G.limitCarrier.carrier → U (G.subsequence k) :=
    e (G.subsequence k) ∘ psi k
  have hpsi (k : ℕ) : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (psi k) (G.exhaustion k) :=
    Poincare.isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv (G.exhaustion_open k)
      (fun x hx =>
        ((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hx).contMDiffWithinAt)
      (fun x hx => (G.embedding k).spatialMap_mfderiv_bijective (G.exhaustion_open k) hzero hx)
  have ha (k : ℕ) : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (a k) (G.exhaustion k) := by
    intro x
    exact (hpsi k x).comp (𝓡 3) (U (G.subsequence k))
      ((e (G.subsequence k)).isLocalDiffeomorph (psi k x.val))
  have hemb (k : ℕ) : Topology.IsOpenEmbedding (fun x : G.exhaustion k => a k x.val) :=
    (e (G.subsequence k)).toHomeomorph.isOpenEmbedding.comp
      ((G.embedding k).spatialHomeomorph (G.exhaustion_open k) hzero).isOpenEmbedding_restrict
  let Eshort (k : ℕ) := Cylinder.restrict
    (V := (U (G.subsequence k) : Set (D (G.subsequence k)).carrier))
    (E (G.subsequence k)).embedding htauBig (Subset.refl _)
  let out (k : ℕ) := liftCylinderOfOrdinaryEmbedding L0 (U (G.subsequence k))
    (Eshort k) (G.exhaustion k) (G.exhaustion_open k) (a k) (hemb k) (ha k)
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
    time := fun _ => tau
    time_pos := fun _ => htau
    time_increasing := monotone_const
    time_subset := fun _ => Subset.refl _
    time_cofinal := fun _ _ hI => Eventually.of_forall fun _ => hI }
  have hzeroTau : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨by linarith, le_rfl⟩
  have hbase (k : ℕ) : a k G.limitFlow.base = p (G.subsequence k) := by
    have hb := congrArg Prod.snd (G.base_preserving k)
    change psi k G.limitFlow.base = (H.sequence.flow (G.subsequence k)).base at hb
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
    change (E (G.subsequence k)).embedding.pointMap 0 (htauBig h0)
      (a k G.limitFlow.base).val = S.base (sigma (G.subsequence k))
    rw [hbase]
    exact (E (G.subsequence k)).zero_identity _ (p (G.subsequence k)).val
      (p (G.subsequence k)).property
  · intro A hA
    let C : ℝ := (3 : ℝ) ^ 3 * max B 1
    let R : ℝ := Real.exp (C * Tbig) * A
    have hC : 0 ≤ C := mul_nonneg (by positivity) (zero_le_one.trans (le_max_right B 1))
    have hR : 0 < R := mul_pos (Real.exp_pos _) hA
    have hRic (i : ℕ) (t : ℝ) (ht : t ∈ Icc (-Tbig) 0)
        (x : (H.sequence.carrier i).carrier) (w : TangentSpace (𝓡 3) x) :
        |((Fbig i).connection t).ricci x w w| ≤ C * ((Fbig i).metric t).inner x w w := by
      have hQ : 0 ≤ ((Fbig i).metric t).inner x w w := by
        by_cases hw : w = 0
        · subst w; simp
        · exact (((Fbig i).metric t).pos x w hw).le
      have hnorm := ((Fbig i).connection t).abs_ricci_quadratic_le_curvatureTensorNorm x w
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := finrank_euclideanSpace_fin
      simp only [Fintype.card_fin, hdim] at hnorm
      exact hnorm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((hcurv i t ht x).trans (le_max_left B 1))
          (by positivity)) hQ)
    have hgrowth : ∀ᶠ k : ℕ in atTop, A < W (G.subsequence k) := by
      obtain ⟨N, hN⟩ := exists_nat_ge A
      filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually
        (eventually_ge_atTop N)] with k hk
      have hNk : (N : ℝ) ≤ (G.subsequence k : ℝ) := by exact_mod_cast hk
      dsimp [W]
      linarith
    have hcover := G.eventually_source_ball_subset_image_ball hzero hzero hcomplete
      hR (show (1 : ℝ) < 2 by norm_num)
    have hclosed : IsCompact (closure ((G.limitFlow.metricAt 0).ball G.limitFlow.base (2 * R))) :=
      (G.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hcomplete
        G.limitFlow.base (2 * R)
    obtain ⟨N, hN⟩ := G.exists_exhaustion_superset hclosed
    filter_upwards [hgrowth, hcover, eventually_ge_atTop N] with k hk hcover hkN x hx
    have hcontained : (gbar (G.subsequence k)).ball (S.base (sigma (G.subsequence k))).2 A ⊆
        U (G.subsequence k) := by
      intro y hy
      change y ∈ S.baseBall (sigma (G.subsequence k)) (W (G.subsequence k))
      rw [← scaled_terminal_ball_eq_baseBall]
      exact hy.trans_le (ENNReal.ofReal_le_ofReal hk.le)
    have hxbar : x ∈ (gbar (G.subsequence k)).ball (S.base (sigma (G.subsequence k))).2 A := by
      rwa [scaled_terminal_ball_eq_baseBall]
    let xu : U (G.subsequence k) := ⟨x, hcontained hxbar⟩
    have hxu : xu ∈ ((O (G.subsequence k)).metric 0).ball (p (G.subsequence k)) A := by
      rw [intrinsic_ball_eq_preimage (gbar (G.subsequence k)) (U (G.subsequence k))
        ((O (G.subsequence k)).metric 0) (hOzero (G.subsequence k))
        (p (G.subsequence k)) hcontained]
      exact hxbar
    let z := (e (G.subsequence k)).symm xu
    have hz : z ∈ ((Fbig (G.subsequence k)).metric 0).ball
        (H.sequence.flow (G.subsequence k)).base A := by
      rw [hball]
      change e (G.subsequence k) ((e (G.subsequence k)).symm xu) ∈
        ((O (G.subsequence k)).metric 0).ball (p (G.subsequence k)) A
      rw [Diffeomorph.apply_symm_apply]
      exact hxu
    have hzeroBig : (0 : ℝ) ∈ Icc (-Tbig) 0 := ⟨by linarith, le_rfl⟩
    have hrefBig : -T / 2 ∈ Icc (-Tbig) (0 : ℝ) := ⟨by linarith, by linarith⟩
    have hcmp := (Fbig (G.subsequence k)).ball_subset_ball_of_ricci_bound
      (convex_Icc (-Tbig) 0) (Subset.refl _) (H.sequence.flow (G.subsequence k)).base
      A C hzeroBig hrefBig (fun t ht y _ w => hRic (G.subsequence k) t ht y w)
    have hdisplacement : |(-T / 2) - (0 : ℝ)| ≤ Tbig := by
      rw [sub_zero, abs_of_neg (by linarith : -T / 2 < 0)]
      linarith
    have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdisplacement hC)
    have hzRef : z ∈ ((Fbig (G.subsequence k)).metric (-T / 2)).ball
        (H.sequence.flow (G.subsequence k)).base R :=
      (hcmp hz).trans_le (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hexp hA.le))
    have href : (Fbig (G.subsequence k)).metric (-T / 2) =
        (H.sequence.flow (G.subsequence k)).metricAt 0 := by
      rw [hmetric]
      congr 1
      ring
    rw [href] at hzRef
    obtain ⟨y, hy, hpy⟩ := hcover hzRef
    have hay : a k y = xu := by
      change e (G.subsequence k) (psi k y) = xu
      change psi k y = z at hpy
      rw [hpy]
      exact (e (G.subsequence k)).apply_symm_apply xu
    refine ⟨ULift.up y, G.exhaustion_monotone hkN (hN (subset_closure hy)), hzeroTau, ?_⟩
    change (E (G.subsequence k)).embedding.pointMap 0 (htauBig hzeroTau) (a k y).val = _
    rw [hay]
    exact (E (G.subsequence k)).zero_identity _ xu.val xu.property
  · dsimp only
    intro q j r K hK hKstage eps heps
    rcases q with ⟨q⟩
    let V := EuclideanSpace ℝ (Fin 3)
    let : NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
    let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
    let Z := ℝ × V
    let Bilin := V →L[ℝ] V →L[ℝ] ℝ
    let c := extChartAt (𝓡 3) q
    let Q := Icc (-tau) (0 : ℝ) ×ˢ c.target
    let f : ℕ → Z → Bilin := fun k z =>
      ((Fbig (G.subsequence k)).metric z.1).pullbackCoefficients (psi k ∘ c.symm) z.2
    let g : Z → Bilin := fun z => (F.metric z.1).pullbackCoefficients c.symm z.2
    have hKQ : K ⊆ Q := by
      intro z hz
      have ht := (hKstage hz).1
      change z ∈ blowupMetricChartDomain (liftBlowupLimit.{u} L0) (ULift.up q) at ht
      rw [liftBlowupLimit_metricChartDomain] at ht
      exact ht
    have hstage (z : Z) (hz : z ∈ K) : c.symm z.2 ∈ G.exhaustion j := (hKstage hz).2
    have hQ : UniqueDiffOn ℝ Q :=
      (uniqueDiffOn_Icc (show -tau < (0 : ℝ) by linarith)).prod
        (isOpen_extChartAt_target (I := 𝓡 3) q).uniqueDiffOn
    have hchart (y : V) (hy : y ∈ c.target) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
      (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy).contMDiffAt
        (extChartAt_target_mem_nhds' hy)
    let Ftau (i : ℕ) : RicciFlow 3 (H.sequence.carrier i).carrier (Icc (-tau) 0) :=
      Poincare.Geometry.RicciFlow.Harnack.restrictFlow (Fbig i)
        htauBig ordConnected_Icc (hne tau htau)
    have hsource : ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, ContDiffWithinAt ℝ ∞ (f k) Q z := by
      filter_upwards [eventually_ge_atTop j] with k hk z hz
      have hmap := (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero
        (G.exhaustion_monotone hk (hstage z hz))
      exact ((Ftau (G.subsequence k)).smooth.contDiffWithinAt_spacetime_pullbackCoefficients
        (hmap.comp z.2 (hchart z.2 (hKQ hz).2)) (hKQ hz).1).mono
          (prod_mono subset_rfl (subset_univ _))
    have hlimit (z : Z) (hz : z ∈ K) : ContDiffWithinAt ℝ ∞ g Q z :=
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
          (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ aa))
      let Evalr := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin r => Z) Bilin ℝ Eval
      have hbilinear : TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ r (f k) Q)
          (iteratedFDerivWithin ℝ r g Q) atTop K := hjets q r K hK hKQ
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
    refine ⟨max j N, le_max_left _ _, ?_⟩
    intro k hk
    have hjk : j ≤ k := (le_max_left _ _).trans hk
    have hNk : N ≤ k := (le_max_right _ _).trans hk
    refine ⟨?_, ?_⟩
    · intro z hz
      have ht := (hKstage hz).1
      exact ht
    · intro aa bb z hz
      have hxs : c.symm z.2 ∈ G.exhaustion k := G.exhaustion_monotone hjk (hstage z hz)
      let Otau (i : ℕ) : RicciFlow 3 (U i) (Icc (-tau) 0) :=
        Poincare.Geometry.RicciFlow.Harnack.restrictFlow (O i)
          htauBig ordConnected_Icc (hne tau htau)
      have hsourceJet := liftCylinder_iteratedFDerivWithin_ordinaryCoefficient
        L0 (U (G.subsequence k)) (Eshort k) (Otau (G.subsequence k))
        (fun t ht x v w => hO (G.subsequence k) t (htauBig ht) x v w)
        (G.exhaustion_open k) (a k) (ha k).contMDiffOn (out k)
        (fun _ _ _ => rfl) q aa bb r z (hKQ hz) hxs
      have htargetJet := liftBlowupLimit_iteratedFDerivWithin_coordinateCoefficient.{u}
        L0 q aa bb r z (hKQ hz)
      have hcoeff : (fun y : Z => f k y (EuclideanSpace.basisFun (Fin 3) ℝ aa)
            (EuclideanSpace.basisFun (Fin 3) ℝ bb)) =
          (fun y : Z => ((Otau (G.subsequence k)).metric y.1).pullbackCoefficients
            (a k ∘ c.symm) y.2 (EuclideanSpace.basisFun (Fin 3) ℝ aa)
              (EuclideanSpace.basisFun (Fin 3) ℝ bb)) := by
        funext y
        have hc := ((O (G.subsequence k)).metric y.1).parametrizedCoefficients_pullbackOfDiffeomorph
          (e (G.subsequence k)) (psi k ∘ c.symm)
        rw [RiemannianMetric.parametrizedCoefficients_eq_pullbackCoefficients,
          RiemannianMetric.parametrizedCoefficients_eq_pullbackCoefficients] at hc
        exact congrArg (fun b => b y.2 (EuclideanSpace.basisFun (Fin 3) ℝ aa)
          (EuclideanSpace.basisFun (Fin 3) ℝ bb)) hc
      rw [hsourceJet, htargetJet, ← hcoeff]
      exact hN k hNk aa bb z hz

end PoincareConjecture.M30
