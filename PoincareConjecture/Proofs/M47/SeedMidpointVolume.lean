import PoincareConjecture.Proofs.M47.JointSeedBallContainment
import PoincareConjecture.Proofs.M34.Standard.LocalCalibratedImageVolume










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]



theorem seed_midpoint_volume_of_metric_bounds
    (g h : RiemannianMetric 3 M) (q : M) {R k : ℝ} (hR : 0 < R)
    (hupper : ∀ x : M, ∀ w : TangentSpace (𝓡 3) x,
      h.inner x w w ≤ g.inner x w w)
    (hlower : ∀ x ∈ closure (g.ball q R), ∀ w : TangentSpace (𝓡 3) x,
      Real.exp (-1 / 4 : ℝ) * g.inner x w w ≤ h.inner x w w)
    (hvolume : ENNReal.ofReal (k * (R / 2) ^ 3) ≤
      calibratedMetricVolume g (g.ball q (R / 2))) :
    ENNReal.ofReal ((k / 8) * (R / 2) ^ 3) ≤
      calibratedMetricVolume h (h.ball q (R / 2)) := by
  have hopen (r : ℝ) : IsOpen (g.ball q r) := by
    let : PseudoEMetricSpace M := g.comparisonPseudoEMetric
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let e := OpenPartialHomeomorph.ofSet (g.ball q R) (hopen R)
  have hnorm : ∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
      g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤ 2 * h.tangentNorm x w := by
    intro x hx w
    change g.tangentNorm x (mfderiv (𝓡 3) (𝓡 3) id x w) ≤ _
    rw [mfderiv_id, ContinuousLinearMap.id_apply]
    exact PoincareConjecture.M47.jointSeed_tangent_reverse_le_two g h x w
      (hlower x (subset_closure hx) w)
  have hsub : g.ball q (R / 2) ⊆ e.source := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith : R / 2 ≤ R))
  have hvol := M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le h g e
    (show ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source from contMDiffOn_id)
    (by norm_num : (0 : ℝ) < 2) hnorm (hopen (R / 2)).measurableSet hsub
  change calibratedMetricVolume g (id '' g.ball q (R / 2)) ≤ _ at hvol
  simp only [image_id] at hvol
  norm_num at hvol
  have hball := (PoincareConjecture.M47.jointSeed_seed_ball_inclusions g h q hR hupper hlower).1
  have hbound := hvolume.trans (hvol.trans (mul_le_mul' le_rfl (measure_mono hball)))
  calc
    ENNReal.ofReal ((k / 8) * (R / 2) ^ 3) =
        ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (k * (R / 2) ^ 3) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (1 / 8 : ℝ) *
        (8 * calibratedMetricVolume h (h.ball q (R / 2))) := mul_le_mul_right hbound _
    _ = calibratedMetricVolume h (h.ball q (R / 2)) := by
      rw [← mul_assoc]
      have hcancel : ENNReal.ofReal (1 / 8 : ℝ) * 8 = 1 := by
        rw [← show ENNReal.ofReal (8 : ℝ) = (8 : ℝ≥0∞) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
        norm_num
      rw [hcancel, one_mul]



theorem seed_midpoint_volume {J : Set ℝ} (F : RicciFlow 3 M J)
    {b v A L R k : ℝ} (q : M) (hR : 0 < R) (hA : 1 ≤ A) (hL : 0 < L)
    (hv : 0 ≤ v) (hJ : Icc b (b + v) ⊆ J)
    (hsec : ∀ s ∈ Icc b (b + v), ∀ x : M, ∀ w z : TangentSpace (𝓡 3) x,
      0 ≤ (F.connection s).curvatureTensor x w z w z)
    (hscalar : ∀ x ∈ closure ((F.metric b).ball q R), ∀ s ∈ Icc b (b + v),
      (F.connection s).scalarCurvature x ≤ 8 * L)
    (hbudget : A * L * v ≤ 1 / 64)
    (hvolume : ENNReal.ofReal (k * (R / 2) ^ 3) ≤
      calibratedMetricVolume (F.metric b) ((F.metric b).ball q (R / 2))) :
    ENNReal.ofReal ((k / 8) * (R / 2) ^ 3) ≤
      calibratedMetricVolume (F.metric (b + v / 2))
        ((F.metric (b + v / 2)).ball q (R / 2)) := by
  have ht : b + v / 2 ∈ Icc b (b + v) := ⟨by linarith, by linarith⟩
  have hmetric := PoincareConjecture.M47.jointSeed_early_metric_bounds F hA hL hv hJ
    hsec hscalar hbudget
  apply seed_midpoint_volume_of_metric_bounds (F.metric b) (F.metric (b + v / 2)) q hR
    (fun x w => PoincareConjecture.M47.jointSeed_metric_upper_of_nonnegative_sectional F ht.1
      ((Icc_subset_Icc le_rfl ht.2).trans hJ)
      (fun s hs => hsec s ((Icc_subset_Icc le_rfl ht.2) hs)) x w)
    (fun x hx w => (hmetric _ ht x hx w).1) hvolume

end PoincareConjecture.Proofs.M47
