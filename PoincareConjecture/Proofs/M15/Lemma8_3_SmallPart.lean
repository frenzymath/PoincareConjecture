import PoincareConjecture.Proofs.M15.Lemma8_3_SmallGeometry
import PoincareConjecture.Proofs.M15.Lemma8_3_Action

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

theorem exists_actualBallCylinder_small_part_bound
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
        (_B : M15ActualBallCylinder G T x r K C),
        IsCompact (closure ((G.slices T).metricOnPoints.ball x r)) →
        ∀ (E : M14ExponentialFamily G T x.val) (epsilon : ℝ),
          0 < epsilon → epsilon ≤ epsilon0 →
          ∀ (H : M14StableSet G T (epsilon * r ^ 2) x.val E)
            (_S : M14ReducedVolumeSourceCoverageData G)
            (A : M14ReducedVolumeAnalyticData G T (epsilon * r ^ 2) x.val E H)
            (W : Set (G.Horizontal x.val)),
            MeasurableSet W → W ⊆ H.carrier →
            (∀ Z, Z ∈ W →
              Real.sqrt (G.spacetime.horizontalMetric.inner x.val Z Z) ≤
                1 / (8 * Real.sqrt epsilon)) →
            calibratedMetricVolume (G.slices T).metricOnPoints
              ((G.slices T).metricOnPoints.ball x r) ≤
              ENNReal.ofReal (epsilon ^ n * r ^ n) →
            M14ReducedVolumeOnAnalyticCarrier A W ≤
              2 * Real.rpow epsilon ((n : ℝ) / 2) := by
  obtain ⟨eg, heg, heghalf, hgeometry⟩ :=
    exists_actualBallCylinder_small_part_geometry hM04 n hM12 hM13
  obtain ⟨en, hen, _, hnumeric⟩ := exists_small_epsilon_exit_bounds (n * n) 0
  refine ⟨min eg en, lt_min heg hen, (min_le_left _ _).trans heghalf, ?_⟩
  intro X _ time I G T x r K C _ _ _ _ _ B hcompact E epsilon hepsilon hepsilon_le
    H S A W hW hWH hsmall hball
  have hr := B.radius_pos
  obtain ⟨hscalar, hfinite, hvolume⟩ := hgeometry X time I G T x r K C B hcompact
    E epsilon hepsilon (hepsilon_le.trans (min_le_left _ _)) H W hWH hsmall
  have hscalar' : ∀ Z ∈ W, ∀ s ∈ Ioo 0 (epsilon * r ^ 2),
      -((n : ℝ) ^ 2 * (r⁻¹) ^ 2) ≤
        horizontalScalarCurvature G.leafwise (E.gamma Z (Real.sqrt s)) := by
    simpa only [neg_mul] using hscalar
  have haction := reducedVolumeOn_le_image_volume S A hW hWH hscalar' hfinite.ne
  have hvolENN := hvolume.trans (mul_le_mul' le_rfl hball)
  have hvolreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)
    hvolENN
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hepsilon.le n) (pow_nonneg hr.le n))]
    at hvolreal
  have hexp : Real.exp ((4 / 3 : ℝ) * (n : ℝ) ^ 2 * epsilon) ≤ 2 := by
    have h := (hnumeric epsilon hepsilon (hepsilon_le.trans (min_le_right _ _))).1
    simp only [Nat.cast_mul] at h
    apply (Real.exp_le_exp.mpr ?_).trans (h.trans (by norm_num))
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hepsilon.le]
  have hcurv : (n : ℝ) ^ 2 * (r⁻¹) ^ 2 * (epsilon * r ^ 2) / 3 =
      (n : ℝ) ^ 2 * epsilon / 3 := by
    field_simp
  have hrpower : Real.rpow (r ^ 2) (-(n : ℝ) / 2) * r ^ n = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r n,
      ← Real.rpow_add hr]
    convert Real.rpow_zero r using 1
    congr 1
    ring
  have hepower : Real.rpow epsilon (-(n : ℝ) / 2) * epsilon ^ n =
      Real.rpow epsilon ((n : ℝ) / 2) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast epsilon n, ← Real.rpow_add hepsilon]
    congr 1
    ring
  have hpower : Real.rpow (epsilon * r ^ 2) (-(n : ℝ) / 2) *
      (epsilon ^ n * r ^ n) = Real.rpow epsilon ((n : ℝ) / 2) := by
    rw [show Real.rpow (epsilon * r ^ 2) (-(n : ℝ) / 2) =
      Real.rpow epsilon (-(n : ℝ) / 2) * Real.rpow (r ^ 2) (-(n : ℝ) / 2) from
        Real.mul_rpow hepsilon.le (sq_nonneg r)]
    calc
      _ = (Real.rpow epsilon (-(n : ℝ) / 2) * epsilon ^ n) *
          (Real.rpow (r ^ 2) (-(n : ℝ) / 2) * r ^ n) := by ring
      _ = _ := by rw [hrpower, mul_one, hepower]
  have hexpproduct : Real.exp ((n : ℝ) ^ 2 * epsilon / 3) *
      Real.exp ((n : ℝ) * epsilon) ^ n =
      Real.exp ((4 / 3 : ℝ) * (n : ℝ) ^ 2 * epsilon) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    M14ReducedVolumeOnAnalyticCarrier A W ≤
        (Real.rpow (epsilon * r ^ 2) (-(n : ℝ) / 2) *
          Real.exp ((n : ℝ) ^ 2 * (r⁻¹) ^ 2 * (epsilon * r ^ 2) / 3)) *
          (Real.exp ((n : ℝ) * epsilon) ^ n * (epsilon ^ n * r ^ n)) :=
      haction.trans (mul_le_mul_of_nonneg_left hvolreal
        (mul_nonneg (Real.rpow_nonneg H.tau_pos.le _) (Real.exp_pos _).le))
    _ = Real.exp ((4 / 3 : ℝ) * (n : ℝ) ^ 2 * epsilon) *
        Real.rpow epsilon ((n : ℝ) / 2) := by
      rw [hcurv]
      calc
        _ = (Real.exp ((n : ℝ) ^ 2 * epsilon / 3) *
            Real.exp ((n : ℝ) * epsilon) ^ n) *
            (Real.rpow (epsilon * r ^ 2) (-(n : ℝ) / 2) *
              (epsilon ^ n * r ^ n)) := by ring
        _ = _ := by rw [hexpproduct, hpower]
    _ ≤ 2 * Real.rpow epsilon ((n : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hepsilon.le _)

end PoincareConjecture.Proofs.M15
