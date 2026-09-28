import PoincareConjecture.Proofs.M15.Lemma8_7_TerminalLiftSpeed
import PoincareConjecture.Proofs.M15.Lemma8_7_ExitConstants
import PoincareConjecture.Proofs.M15.Lemma8_7_SpatialDistance









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15




theorem exists_actualBallCylinder_prefix_displacement_bound
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
          ∀ S : ℝ, 0 < S → S ≤ Real.sqrt tau →
          S ≤ Real.sqrt epsilon * r →
          Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve 0)
            (R.horizontal_velocity 0) (R.horizontal_velocity 0)) ≤
              1 / (4 * Real.sqrt epsilon) →
          (∀ s ∈ Set.Ioo 0 S,
            M14SquareRootEulerResidual G R E s (R.horizontal_velocity s) = 0) →
          ∀ L : ℝ → (G.timeIntervals.interval K).Point × C,
          (∀ s ∈ Set.Icc 0 S, B.embedding.toSpacetime (L s) = R.curve s) →
          (∀ s ∈ Set.Icc 0 S,
            B.source_map (L s).2 ∈ (G.slices T).metricOnPoints.ball x (r / 2)) →
          (G.slices T).metricOnPoints.edist x (B.source_map (L S).2) ≤
            ENNReal.ofReal (5 * r / 12) := by
  obtain ⟨A, hA, hspeed⟩ :=
    exists_actualBallCylinder_lift_terminal_speed_bound hM04 n hM12 hM13
  obtain ⟨epsilon0, hepsilon0, hepsilon0half, hconstants⟩ :=
    exists_small_epsilon_exit_bounds n A
  refine ⟨epsilon0, hepsilon0, hepsilon0half, ?_⟩
  intro X _ time I G T x r K C _ _ _ _ _ B hcompact D tau y p R E epsilon
    hepsilon hepsilon_le S hS hStau hSr hq hEuler L hL hhalf
  have hr := B.radius_pos
  have hw := Real.sqrt_pos.mpr hepsilon
  have hSsq : S ^ 2 ≤ epsilon * r ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt hepsilon.le] using pow_le_pow_left₀ hS.le hSr 2
  have hSrhalf : S ^ 2 ≤ r ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_right (hepsilon_le.trans hepsilon0half) (sq_nonneg r)
    linarith
  obtain ⟨hexp, hAsq⟩ := hconstants epsilon hepsilon hepsilon_le
  have hbound (s : ℝ) (hs : s ∈ Icc 0 S) :
      (B.metric.metric T).tangentNorm (L s).2
        (mfderivWithin 𝓘(ℝ) (𝓡 n) (fun t => (L t).2) (Icc 0 S) s 1) ≤
      5 / (12 * Real.sqrt epsilon) :=
    (hspeed X time I G T x r K C B hcompact D tau y p R E S hS hStau hSrhalf
      hEuler L hL hhalf s hs).trans
        (scaled_squareRoot_speed_le n hA.le hr hepsilon (Real.sqrt_nonneg _) hq
          hs.1 (hs.2.trans hSr) hexp hAsq)
  have hsub : Icc 0 S ⊆ M14SqrtParameterInterval 0 tau := by
    intro s hs
    exact ⟨by simpa only [Real.sqrt_zero] using hs.1, hs.2.trans hStau⟩
  have hsmooth := compatibleCylinder_spatial_lift_contMDiffOn G (G.timeIntervals.interval K)
    B.embedding B.metric (R.smooth.mono (hsub.trans R.interval_subset)) L hL
  have hdist := edist_le_of_tangentNorm_mfderivWithin_le (B.metric.metric T)
    hS.le (by positivity : 0 ≤ 5 / (12 * Real.sqrt epsilon))
    (hsmooth.of_le (by simp)) hbound
  have hlength : 5 / (12 * Real.sqrt epsilon) * S ≤ 5 * r / 12 := by
    calc
      _ ≤ 5 / (12 * Real.sqrt epsilon) * (Real.sqrt epsilon * r) :=
        mul_le_mul_of_nonneg_left hSr (by positivity)
      _ = _ := by field_simp
  have hdist' : (B.metric.metric T).edist (L 0).2 (L S).2 ≤
      ENNReal.ofReal (5 * r / 12) := by
    apply hdist.trans
    simpa only [sub_zero] using ENNReal.ofReal_le_ofReal hlength
  obtain ⟨F, hmetric, hRm, _⟩ := actualBallCylinder_exists_flow hM12 B
  have hsource := actualBallCylinder_terminal_edist_le hM12 B F hmetric hRm
    B.base_mem (L 0).2 (L S).2
  simp only [sub_self, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul, hmetric] at hsource
  have h0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
  have hR0 : R.curve 0 = x.val := by
    simpa only [zero_pow (by decide : 2 ≠ 0), p.curve_start] using R.agrees 0 (hsub h0)
  have ht0 : (L 0).1 = ⟨T, B.base_mem⟩ := by
    apply Subtype.ext
    have h := B.embedding.time_eq (L 0)
    rw [hL 0 h0, hR0] at h
    exact h.symm.trans x.property
  have hbased : B.embedding.toSpacetime (L 0) = (B.source_map (L 0).2).val := by
    calc
      _ = B.embedding.toSpacetime (⟨T, B.base_mem⟩, (L 0).2) :=
        congrArg B.embedding.toSpacetime (Prod.ext ht0 rfl)
      _ = _ := B.based (L 0).2
  have hstart : B.source_map (L 0).2 = x :=
    Subtype.ext (hbased.symm.trans ((hL 0 h0).trans hR0))
  calc
    _ = (G.slices T).metricOnPoints.edist (B.source_map (L 0).2)
        (B.source_map (L S).2) :=
      congrArg (fun z => (G.slices T).metricOnPoints.edist z (B.source_map (L S).2)) hstart.symm
    _ ≤ _ := hsource.trans hdist'

end PoincareConjecture.Proofs.M15
