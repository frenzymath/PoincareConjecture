import PoincareConjecture.Proofs.M15.Lemma8_7_ActualConfinement

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

theorem exists_actualBallCylinder_exponential_confinement
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
        ∀ (E : M14ExponentialFamily G T x.val) (epsilon : ℝ),
          0 < epsilon → epsilon ≤ epsilon0 →
          ∀ (a : ℝ), 0 < a → ∀ Z : G.Horizontal x.val,
          (Z, a) ∈ E.domain → ∀ S : ℝ, 0 ≤ S → S ≤ a →
          S ≤ Real.sqrt epsilon * r →
          Real.sqrt (G.spacetime.horizontalMetric.inner x.val Z Z) ≤
            1 / (8 * Real.sqrt epsilon) →
          ∃ L : ℝ → (G.timeIntervals.interval K).Point × C,
            ContMDiffOn 𝓘(ℝ) (spacetimeModel n) ∞ L (Set.Icc 0 S) ∧
            ∀ s ∈ Set.Icc 0 S,
              B.embedding.toSpacetime (L s) = E.gamma Z s ∧
              (G.slices T).metricOnPoints.edist x (B.source_map (L s).2) ≤
                ENNReal.ofReal (5 * r / 12) ∧
              B.source_map (L s).2 ∈ (G.slices T).metricOnPoints.ball x (r / 2) := by
  obtain ⟨epsilon0, hepsilon0, hepsilon0half, hconf⟩ :=
    exists_actualBallCylinder_confinement hM04 n hM12 hM13
  refine ⟨epsilon0, hepsilon0, hepsilon0half, ?_⟩
  intro X _ time I G T x r K C _ _ _ _ _ B hcompact E epsilon hepsilon hepsilon_le
    a ha Z hZa S hS hSa hSr hZ
  obtain ⟨D⟩ := ((hM12.leafwise_calculus X time I G.spacetime G.slices G.timeIntervals
    G.gaugeCover).2 G.leafwise).horizontal_connection
  let R := E.square_path Z a hZa ha
  let E₁ := E.square_extension Z a hZa ha
  obtain ⟨hzero, hvelocity⟩ := E.square_initial_velocity Z a hZa ha
  have htransport (z : G.Point) (h : R.curve 0 = z) :
      G.spacetime.horizontalMetric.inner (R.curve 0)
          (R.horizontal_velocity 0) (R.horizontal_velocity 0) =
        G.spacetime.horizontalMetric.inner z (h ▸ R.horizontal_velocity 0)
          (h ▸ R.horizontal_velocity 0) := by
    cases h
    rfl
  have hpair := htransport x.val hzero
  rw [hvelocity] at hpair
  have hpair' : G.spacetime.horizontalMetric.inner x.val ((2 : ℝ) • Z) ((2 : ℝ) • Z) =
      4 * G.spacetime.horizontalMetric.inner x.val Z Z := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hinitial : Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve 0)
      (R.horizontal_velocity 0) (R.horizontal_velocity 0)) ≤
      1 / (4 * Real.sqrt epsilon) := by
    rw [hpair, hpair', Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt 4 = (2 : ℝ) by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
    calc
      _ ≤ 2 * (1 / (8 * Real.sqrt epsilon)) :=
        mul_le_mul_of_nonneg_left hZ (by norm_num)
      _ = 1 / (4 * Real.sqrt epsilon) := by
        field_simp [ne_of_gt (Real.sqrt_pos.mpr hepsilon)]
        norm_num
  have hStau : S ≤ Real.sqrt (a ^ 2) := by rwa [Real.sqrt_sq ha.le]
  have hsub : Icc 0 S ⊆ M14SqrtParameterInterval 0 (a ^ 2) := by
    intro s hs
    exact ⟨by simpa only [Real.sqrt_zero] using hs.1, hs.2.trans hStau⟩
  have hEuler (s : ℝ) (hs : s ∈ Ioo 0 S) :
      M14SquareRootEulerResidual G R E₁ s (R.horizontal_velocity s) = 0 :=
    E.square_euler Z a hZa ha s (hsub ⟨hs.1.le, hs.2.le⟩) (R.horizontal_velocity s)
  obtain ⟨L, hLs, hL⟩ := hconf X time I G T x r K C B hcompact D (a ^ 2) (E.gamma Z a)
    (E.path Z a hZa ha) R E₁ epsilon hepsilon hepsilon_le S hS hStau hSr hinitial hEuler
  refine ⟨L, hLs, ?_⟩
  intro s hs
  refine ⟨(hL s hs).1.trans ?_, (hL s hs).2⟩
  calc
    R.curve s = (E.path Z a hZa ha).curve (s ^ 2) := R.agrees s (hsub hs)
    _ = E.gamma Z (Real.sqrt (s ^ 2)) :=
      E.path_coherent Z a hZa ha (s ^ 2)
        ⟨sq_nonneg s, pow_le_pow_left₀ hs.1 (hs.2.trans hSa) 2⟩
    _ = E.gamma Z s := by rw [Real.sqrt_sq hs.1]

end PoincareConjecture.Proofs.M15
