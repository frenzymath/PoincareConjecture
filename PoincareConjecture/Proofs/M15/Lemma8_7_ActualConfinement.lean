import PoincareConjecture.Proofs.M15.Lemma8_7_CompactContinuation
import PoincareConjecture.Proofs.M15.Lemma8_7_PrefixDisplacement

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

theorem exists_actualBallCylinder_confinement
    (hM04 : RicciFlowCurvatureTheory.{u}) (n : ℕ)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
        (I : SpacetimeInterval) (G : GeneralizedLGeometryTransport n X time I)
        (T : ℝ) (x : (G.slices T).Point) (r : ℝ) (K : SpacetimeInterval)
        (C : Type u) [TopologicalSpace C]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
        [T2Space C] [SecondCountableTopology C]
        (B : M15ActualBallCylinder G T x r K C),
        IsCompact (closure ((G.slices T).metricOnPoints.ball x r)) →
        ∀ (_D : SpacetimeHorizontalConnection G.leafwise)
          (tau : ℝ) (y : G.Point) (p : M14BackwardPath G T 0 tau x.val y)
          (R : M14SquareRootPath G p)
          (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 tau)
            R.horizontal_velocity)
          (epsilon : ℝ), 0 < epsilon → epsilon ≤ epsilon0 →
          ∀ S : ℝ, 0 ≤ S → S ≤ Real.sqrt tau →
          S ≤ Real.sqrt epsilon * r →
          Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve 0)
            (R.horizontal_velocity 0) (R.horizontal_velocity 0)) ≤
              1 / (4 * Real.sqrt epsilon) →
          (∀ s ∈ Set.Ioo 0 S,
            M14SquareRootEulerResidual G R E s (R.horizontal_velocity s) = 0) →
          ∃ L : ℝ → (G.timeIntervals.interval K).Point × C,
            ContMDiffOn 𝓘(ℝ) (spacetimeModel n) ∞ L (Set.Icc 0 S) ∧
            ∀ s ∈ Set.Icc 0 S,
              B.embedding.toSpacetime (L s) = R.curve s ∧
              (G.slices T).metricOnPoints.edist x (B.source_map (L s).2) ≤
                ENNReal.ofReal (5 * r / 12) ∧
              B.source_map (L s).2 ∈ (G.slices T).metricOnPoints.ball x (r / 2) := by
  obtain ⟨epsilon0, hepsilon0, hepsilon0half, hdisplacement⟩ :=
    exists_actualBallCylinder_prefix_displacement_bound hM04 n hM12 hM13
  refine ⟨epsilon0, hepsilon0, hepsilon0half, ?_⟩
  intro X _ time I G T x r K C _ _ _ _ _ B hcompact D tau y p R E epsilon
    hepsilon hepsilon_le S hS hStau hSr hq hEuler
  have hr := B.radius_pos
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : (G.slices T).Point → Type _) :=
    ⟨(G.slices T).metricOnPoints.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : (G.slices T).Point → Type _) :=
    ⟨⟨(G.slices T).metricOnPoints.inner,
      (G.slices T).metricOnPoints.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace (G.slices T).Point :=
    .ofRiemannianMetric (𝓡 n) (G.slices T).Point
  have hball (a : ℝ) : (G.slices T).metricOnPoints.ball x a =
      Metric.eball x (ENNReal.ofReal a) := by
    ext z
    change edist x z < _ ↔ edist z x < _
    rw [edist_comm x z]
  let U := B.source_map ⁻¹' (G.slices T).metricOnPoints.ball x (r / 2)
  let A := B.source_map ⁻¹' Metric.closedEBall x (ENNReal.ofReal (5 * r / 12))
  have hU : IsOpen U := by
    dsimp only [U]
    rw [hball]
    exact Metric.isOpen_eball.preimage B.source_map_embedding.continuous
  have hsmall : ENNReal.ofReal (5 * r / 12) < ENNReal.ofReal (r / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hfull : Metric.closedEBall x (ENNReal.ofReal (5 * r / 12)) ⊆
      (G.slices T).metricOnPoints.ball x r := by
    rw [hball]
    intro z hz
    exact (Metric.mem_closedEBall.mp hz).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
  have hAcompact : IsCompact A :=
    B.source_map_embedding.isInducing.isCompact_preimage'
      (hcompact.of_isClosed_subset Metric.isClosed_closedEBall (hfull.trans subset_closure))
      (by rw [B.source_map_range]; exact hfull)
  have hAU : A ⊆ U := by
    intro c hc
    change B.source_map c ∈ (G.slices T).metricOnPoints.ball x (r / 2)
    rw [hball]
    exact (Metric.mem_closedEBall.mp hc).trans_lt hsmall
  have hxball : x ∈ (G.slices T).metricOnPoints.ball x r := by
    rw [hball]
    exact Metric.mem_eball_self (ENNReal.ofReal_pos.mpr hr)
  obtain ⟨c, hc⟩ := B.source_map_range.symm ▸ hxball
  let q : (G.timeIntervals.interval K).Point × C := (⟨T, B.base_mem⟩, c)
  have hcA : c ∈ A := by
    change edist (B.source_map c) x ≤ _
    rw [hc, edist_self]
    exact bot_le
  have hsub : Icc 0 S ⊆ M14SqrtParameterInterval 0 tau := by
    intro s hs
    exact ⟨by simpa only [Real.sqrt_zero] using hs.1, hs.2.trans hStau⟩
  have h0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS⟩
  have hR0 : R.curve 0 = x.val := by
    simpa only [zero_pow (by decide : 2 ≠ 0), p.curve_start] using R.agrees 0 (hsub h0)
  have hzero : R.curve 0 = B.embedding.toSpacetime q := by
    rw [hR0, B.based c, hc]
  have htime (s : ℝ) (hs : s ∈ Icc 0 S) :
      G.spacetime.timeFunction (R.curve s) ∈ K.domain := by
    rw [R.curve_time s (hsub hs), B.interval_domain]
    have hsquare : s ^ 2 ≤ epsilon * r ^ 2 := by
      simpa only [mul_pow, Real.sq_sqrt hepsilon.le] using
        pow_le_pow_left₀ hs.1 (hs.2.trans hSr) 2
    have he := mul_le_mul_of_nonneg_right (hepsilon_le.trans hepsilon0half) (sq_nonneg r)
    constructor <;> nlinarith [sq_nonneg s, sq_nonneg r]
  have htrap (b : ℝ) (hb : b ∈ Ioc 0 S)
      (hprefix : ∀ s ∈ Icc 0 b,
        R.curve s ∈ B.embedding.toSpacetime '' (univ ×ˢ U)) :
      R.curve b ∈ B.embedding.toSpacetime '' (univ ×ˢ A) := by
    let : Nonempty ((G.timeIntervals.interval K).Point × C) := ⟨q⟩
    let L := fun s => Function.invFun B.embedding.toSpacetime (R.curve s)
    have hL (s : ℝ) (hs : s ∈ Icc 0 b) : B.embedding.toSpacetime (L s) = R.curve s := by
      apply Function.invFun_eq
      obtain ⟨z, _, hz⟩ := hprefix s hs
      exact ⟨z, hz⟩
    have hhalf (s : ℝ) (hs : s ∈ Icc 0 b) :
        B.source_map (L s).2 ∈ (G.slices T).metricOnPoints.ball x (r / 2) := by
      obtain ⟨z, hz, hez⟩ := hprefix s hs
      have hLz : L s = z := B.embedding.embedding.injective ((hL s hs).trans hez.symm)
      rw [hLz]
      exact hz.2
    have hd := hdisplacement X time I G T x r K C B hcompact D tau y p R E epsilon
      hepsilon hepsilon_le b hb.1 (hb.2.trans hStau) (hb.2.trans hSr) hq
      (fun s hs => hEuler s ⟨hs.1, hs.2.trans_le hb.2⟩) L hL hhalf
    refine ⟨L b, ⟨mem_univ _, ?_⟩, hL b ⟨hb.1.le, le_rfl⟩⟩
    change edist (B.source_map (L b).2) x ≤ _
    rw [edist_comm]
    exact hd
  have hK : IsCompact K.domain := by rw [B.interval_domain]; exact isCompact_Icc
  obtain ⟨L, _, hLs, hL⟩ := compatibleCylinder_lift_of_compact_prefix_trap G
    (G.timeIntervals.interval K) B.embedding B.metric hK hU hAcompact hAU q hcA hS R.curve
    (R.smooth.mono (hsub.trans R.interval_subset)) hzero htime htrap
  refine ⟨L, hLs, ?_⟩
  intro s hs
  refine ⟨(hL s hs).1, ?_, hAU (hL s hs).2⟩
  change edist x (B.source_map (L s).2) ≤ _
  rw [edist_comm]
  exact (hL s hs).2

end PoincareConjecture.Proofs.M15
