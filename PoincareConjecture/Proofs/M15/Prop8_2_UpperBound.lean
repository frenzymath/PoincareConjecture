import PoincareConjecture.Proofs.M15.Lemma8_3_SmallPart
import PoincareConjecture.Proofs.M15.Lemma8_9_LargePart

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

theorem exists_actualBallCylinder_reducedVolume_bound
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
            calibratedMetricVolume (G.slices T).metricOnPoints
              ((G.slices T).metricOnPoints.ball x r) ≤
              ENNReal.ofReal (epsilon ^ n * r ^ n) →
            M14ReducedVolumeOnAnalyticCarrier A W ≤
              3 * Real.rpow epsilon ((n : ℝ) / 2) := by
  obtain ⟨es, hes, heshalf, hsmall⟩ :=
    exists_actualBallCylinder_small_part_bound hM04 n hM12 hM13
  obtain ⟨el, hel, hlarge⟩ := exists_large_vector_threshold.{u} n
  refine ⟨min es el, lt_min hes hel, (min_le_left _ _).trans heshalf, ?_⟩
  intro X _ time I G T x r K C _ _ _ _ _ B hcompact E epsilon hepsilon hepsilon_le
    H S A W hW hWH hball
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have henergy : Measurable (fun Z => G.spacetime.horizontalMetric.inner x.val Z Z) := by
    have hcont : Continuous (fun Z => G.spacetime.horizontalMetric.inner x.val Z Z) := by
      fun_prop
    exact hcont.measurable
  let W1 := W ∩ {Z | G.spacetime.horizontalMetric.inner x.val Z Z ≤ 1 / (64 * epsilon)}
  let W2 := W \ W1
  have hW1 : MeasurableSet W1 := hW.inter (measurableSet_le henergy measurable_const)
  have hW2 : MeasurableSet W2 := hW.diff hW1
  have hW1H : W1 ⊆ H.carrier := fun _ hZ => hWH hZ.1
  have hW2H : W2 ⊆ H.carrier := fun _ hZ => hWH hZ.1
  have hcut : (1 / (8 * Real.sqrt epsilon)) ^ 2 = 1 / (64 * epsilon) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hepsilon.le]
    norm_num
  have hsmall' := hsmall X time I G T x r K C B hcompact E epsilon hepsilon
    (hepsilon_le.trans (min_le_left _ _)) H S A W1 hW1 hW1H
    (fun Z hZ => Real.sqrt_le_iff.mpr ⟨by positivity, by rw [hcut]; exact hZ.2⟩) hball
  have hlarge' := hlarge epsilon hepsilon (hepsilon_le.trans (min_le_right _ _))
    S A hW2 hW2H (fun Z hZ => by
      have hnot : ¬ G.spacetime.horizontalMetric.inner x.val Z Z ≤ 1 / (64 * epsilon) :=
        fun h => hZ.2 ⟨hZ.1, h⟩
      exact (lt_of_not_ge hnot).le)
  have hdisjoint : Disjoint W1 W2 := disjoint_left.mpr fun _ hZ1 hZ2 => hZ2.2 hZ1
  have hparts : W1 ∪ W2 = W := by
    ext Z
    simp only [W1, W2, mem_union, mem_inter_iff, mem_ofPred_eq, mem_sdiff]
    tauto
  have hadd := ((S.disjoint_image_additivity T (epsilon * r ^ 2) x.val E H A).2
    W1 W2 hW1H hW2H hW1 hW2 hdisjoint).2.2.2.2
  rw [hparts] at hadd
  rw [hadd]
  linarith

end PoincareConjecture.Proofs.M15
