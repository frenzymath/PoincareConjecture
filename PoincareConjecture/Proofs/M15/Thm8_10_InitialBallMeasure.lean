import PoincareConjecture.Proofs.M15.Thm8_10_EarlyVolume










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M15




theorem exists_compact_initial_ball_volume_bound
    (n : ℕ) (hn : 0 < n) (omega : ℝ) (homega : 0 < omega) :
    ∃ V : ℝ, 0 < V ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
        [CompactSpace M] (T : ℝ) (_hT : 0 < T)
        (F : RicciFlow n M (Icc 0 T)),
        (∀ q, (F.connection 0).curvatureTensorNorm q ≤ 1) →
        (∀ q, ENNReal.ofReal omega ≤
          calibratedMetricVolume (F.metric 0) ((F.metric 0).ball q 1)) →
        ∀ t ∈ Icc 0 (min T (1 / (32 * (n : ℝ) ^ 6))),
        ∀ p : M, ENNReal.ofReal V ≤
          calibratedMetricVolume (F.metric t) ((F.metric 0).ball p 1) := by
  let delta : ℝ := 1 / (32 * (n : ℝ) ^ 6)
  let C : ℝ := Real.exp (2 * (n : ℝ) * delta)
  have hC : 0 < C := Real.exp_pos _
  refine ⟨omega / C ^ n, div_pos homega (pow_pos hC n), ?_⟩
  intro M _ _ _ _ _ _ _ _ T hT F hinit hvolume t ht p
  have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have htDelta : t ≤ delta := ht.2.trans (min_le_right _ _)
  have hnorm (q : M) (w : TangentSpace (𝓡 n) q) :
      (F.metric 0).tangentNorm q w ≤ C * (F.metric t).tangentNorm q w := by
    have hn := M04.tangentNorm_comparison_at_of_curvature_bound F
      (show 0 ∈ Icc 0 T from ⟨le_rfl, hT.le⟩) htT ht.1 (by norm_num : (0 : ℝ) ≤ 2) q
      (fun s hs => compact_curvature_le_two_of_initial_bound hn hT F hinit s
        ⟨hs.1, hs.2.trans ht.2⟩ q) w
    have h := mul_le_mul_of_nonneg_left hn.1
      (Real.exp_pos ((n : ℝ) * 2 * (t - 0))).le
    have he : Real.exp ((n : ℝ) * 2 * (t - 0)) *
        Real.exp (-(n : ℝ) * 2 * (t - 0)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rw [← mul_assoc, he, one_mul] at h
    apply h.trans (mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _))
    apply Real.exp_le_exp.mpr
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hopen : IsOpen ((F.metric 0).ball p 1) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨(F.metric 0).inner, (F.metric 0).toContinuousRiemannianMetric.continuous,
        fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    have hc : Continuous (fun q => (F.metric 0).edist p q) :=
      continuous_const.edist continuous_id
    exact isOpen_lt hc continuous_const
  have hmeasure : calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p 1) ≤
      ENNReal.ofReal C ^ n *
        calibratedMetricVolume (F.metric t) ((F.metric 0).ball p 1) := by
    rw [calibratedMetricVolume_eq_volumeMeasure, calibratedMetricVolume_eq_volumeMeasure]
    have hm := (F.metric t).volumeMeasure_image_le_of_tangentNorm_le (F.metric 0)
      (OpenPartialHomeomorph.refl M) isOpen_univ (subset_refl _) contMDiff_id.contMDiffOn hC
      (fun q _ w => by
        change (F.metric 0).tangentNorm q (mfderiv (𝓡 n) (𝓡 n) id q w) ≤
          C * (F.metric t).tangentNorm q w
        simpa only [mfderiv_id, ContinuousLinearMap.id_apply] using hnorm q w)
      hopen.measurableSet (subset_univ _)
    change (F.metric 0).volumeMeasure (id '' (F.metric 0).ball p 1) ≤ _ at hm
    simpa only [image_id] using hm
  apply (ENNReal.mul_le_mul_iff_right
    (pow_ne_zero n (ENNReal.ofReal_pos.mpr hC).ne')
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp
  calc
    _ = ENNReal.ofReal omega := by
      rw [← ENNReal.ofReal_pow hC.le,
        ← ENNReal.ofReal_mul' (div_pos homega (pow_pos hC n)).le]
      congr 1
      exact mul_div_cancel₀ omega (pow_ne_zero n hC.ne')
    _ ≤ calibratedMetricVolume (F.metric 0) ((F.metric 0).ball p 1) := hvolume p
    _ ≤ _ := hmeasure

end PoincareConjecture.Proofs.M15
