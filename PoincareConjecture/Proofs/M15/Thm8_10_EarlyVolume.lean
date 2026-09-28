import PoincareConjecture.Proofs.M15.Thm8_10_DoublingTime
import PoincareConjecture.Proofs.M15.Thm1_34_VolumeComparison
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M15




theorem calibrated_ball_lower_bound_of_tangentNorm_comparison
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (g h : RiemannianMetric n M) (p : M) {C v r : ℝ}
    (hC : 1 ≤ C) (hv : 0 ≤ v) (hr : 0 < r) (hr1 : r ≤ 1)
    (hforward : ∀ q (w : TangentSpace (𝓡 n) q),
      h.tangentNorm q w ≤ C * g.tangentNorm q w)
    (hbackward : ∀ q (w : TangentSpace (𝓡 n) q),
      g.tangentNorm q w ≤ C * h.tangentNorm q w)
    (hvolume : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ENNReal.ofReal (v * s ^ n) ≤ calibratedMetricVolume g (g.ball p s)) :
    ENNReal.ofReal ((v / C ^ (2 * n)) * r ^ n) ≤
      calibratedMetricVolume h (h.ball p r) := by
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hCp).ne'
  have hdist (q : M) : h.edist p q ≤ ENNReal.ofReal C * g.edist p q := by
    apply g.edist_le_mul_of_tangentNorm_mfderiv_le h
      (F := id) contMDiff_id hCp _ p q
    intro z w
    simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using hforward z w
  have hball : g.ball p (r / C) ⊆ h.ball p r := by
    intro q hq
    have hlt := ENNReal.mul_lt_mul_right hC0 ENNReal.ofReal_ne_top hq
    have heq : ENNReal.ofReal C * ENNReal.ofReal (r / C) = ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul hCp.le, mul_div_cancel₀ r hCp.ne']
    exact (hdist q).trans_lt (hlt.trans_eq heq)
  have hmeasure : calibratedMetricVolume g (g.ball p (r / C)) ≤
      ENNReal.ofReal C ^ n * calibratedMetricVolume h (g.ball p (r / C)) := by
    have hopen : IsOpen (g.ball p (r / C)) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
      let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
      have hc : Continuous (fun q => g.edist p q) := continuous_const.edist continuous_id
      exact isOpen_lt hc continuous_const
    rw [calibratedMetricVolume_eq_volumeMeasure, calibratedMetricVolume_eq_volumeMeasure]
    have hm := h.volumeMeasure_image_le_of_tangentNorm_le g (OpenPartialHomeomorph.refl M)
      isOpen_univ (subset_refl _) contMDiff_id.contMDiffOn hCp
      (fun q _ w => by
        change g.tangentNorm q (mfderiv (𝓡 n) (𝓡 n) id q w) ≤ C * h.tangentNorm q w
        simpa only [mfderiv_id, ContinuousLinearMap.id_apply] using hbackward q w)
      hopen.measurableSet (subset_univ _)
    change g.volumeMeasure (id '' g.ball p (r / C)) ≤ _ at hm
    simpa only [image_id] using hm
  have hsmall : 0 < r / C := div_pos hr hCp
  have hsmall1 : r / C ≤ 1 := (div_le_iff₀ hCp).mpr (by simpa only [one_mul] using hr1.trans hC)
  have hleft : 0 ≤ (v / C ^ (2 * n)) * r ^ n :=
    mul_nonneg (div_nonneg hv (pow_nonneg hCp.le _)) (pow_nonneg hr.le _)
  apply (ENNReal.mul_le_mul_iff_right (pow_ne_zero n hC0)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp
  calc
    _ = ENNReal.ofReal (v * (r / C) ^ n) := by
      rw [← ENNReal.ofReal_pow hCp.le, ← ENNReal.ofReal_mul' hleft]
      congr 1
      rw [div_pow, show 2 * n = n + n by omega, pow_add]
      field_simp
    _ ≤ calibratedMetricVolume g (g.ball p (r / C)) := hvolume _ hsmall hsmall1
    _ ≤ ENNReal.ofReal C ^ n * calibratedMetricVolume h (g.ball p (r / C)) := hmeasure
    _ ≤ _ := mul_le_mul_right (measure_mono hball) _




theorem exists_compact_initial_volume_bound
    (n : ℕ) (hn : 0 < n) (omega : ℝ) (homega : 0 < omega) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
        [CompactSpace M] (T : ℝ) (_hT : 0 < T)
        (F : RicciFlow n M (Icc 0 T)),
        (∀ q, (F.connection 0).curvatureTensorNorm q ≤ 1) →
        (∀ q, ENNReal.ofReal omega ≤
          calibratedMetricVolume (F.metric 0) ((F.metric 0).ball q 1)) →
        ∀ t ∈ Icc 0 (min T (1 / (32 * (n : ℝ)^6))),
        ∀ (p : M) (r : ℝ), 0 < r → r ≤ 1 →
          ENNReal.ofReal (kappa * r ^ n) ≤
            calibratedMetricVolume (F.metric t) ((F.metric t).ball p r) := by
  let delta : ℝ := 1 / (32 * (n : ℝ)^6)
  let C : ℝ := Real.exp (2 * (n : ℝ) * delta)
  let v : ℝ := (RiemannianMetric.euclideanUnitBallVolume n /
    RiemannianMetric.modelVolume n 1 1) * omega
  have hdelta : 0 < delta := by have : 0 < (n : ℝ) := Nat.cast_pos.mpr hn; positivity
  have hC : 1 ≤ C := Real.one_le_exp (mul_nonneg (by positivity) hdelta.le)
  have hCp : 0 < C := Real.exp_pos _
  have hv : 0 < v := mul_pos
    (div_pos (RiemannianMetric.euclideanUnitBallVolume_pos n)
      (RiemannianMetric.modelVolume_pos hn (by norm_num) (by norm_num))) homega
  refine ⟨v / C ^ (2 * n), div_pos hv (pow_pos hCp _), ?_⟩
  intro M _ _ _ _ _ _ _ _ T hT F hinit hvolume t ht p r hr hr1
  have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have htDelta : t ≤ delta := ht.2.trans (min_le_right _ _)
  have hnorm (q : M) (w : TangentSpace (𝓡 n) q) :=
    M04.tangentNorm_comparison_at_of_curvature_bound F (by exact ⟨le_rfl, hT.le⟩)
      htT ht.1 (by norm_num : (0 : ℝ) ≤ 2) q
      (fun s hs => compact_curvature_le_two_of_initial_bound hn hT F hinit s
        ⟨hs.1, hs.2.trans ht.2⟩ q) w
  have hexp : Real.exp ((n : ℝ) * 2 * (t - 0)) ≤ C := by
    apply Real.exp_le_exp.mpr
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  apply calibrated_ball_lower_bound_of_tangentNorm_comparison (F.metric 0) (F.metric t) p
    hC hv.le hr hr1
  · intro q w
    exact (hnorm q w).2.trans
      (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _))
  · intro q w
    have h := mul_le_mul_of_nonneg_left (hnorm q w).1
      (Real.exp_pos ((n : ℝ) * 2 * (t - 0))).le
    have he : Real.exp ((n : ℝ) * 2 * (t - 0)) *
        Real.exp (-(n : ℝ) * 2 * (t - 0)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rw [← mul_assoc, he, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _))
  · intro s hs hs1
    exact calibrated_small_ball_lower_bound_of_unit_volume (F.metric 0) (F.connection 0) p
      hn (by norm_num) homega hinit (hvolume p) hs hs1

end PoincareConjecture.Proofs.M15
