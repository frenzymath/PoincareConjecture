import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.SignedIntegral

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology Bundle

namespace Poincare.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem integrable_polar_comp (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ} (hf : Integrable f μ) :
    Integrable (fun p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) =>
      f ((p.2 : ℝ) • (p.1 : E)))
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  have hms : MeasurableSet ({0}ᶜ : Set E) := (measurableSet_singleton (0 : E)).compl
  have hi := (integrableOn_iff_comap_subtypeVal hms).mp hf.integrableOn
  apply (μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (Homeomorph.measurableEmbedding _)).mp
  convert hi using 1
  ext x
  have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.2 x.2
  simp [smul_smul, mul_inv_cancel₀ hn]

private theorem integral_volumeIoiPow_eq (k : ℕ) (f : ℝ → ℝ) :
    (∫ t : Ioi (0 : ℝ), f t ∂Measure.volumeIoiPow k) =
      ∫ t in Ioi (0 : ℝ), t ^ k * f t := by
  have hdens : Measurable (fun t : Ioi (0 : ℝ) => ENNReal.ofReal ((t : ℝ) ^ k)) := by
    fun_prop
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul hdens
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ t : Ioi (0 : ℝ), (t : ℝ) ^ k * f t ∂Measure.comap Subtype.val volume := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [ENNReal.toReal_ofReal (pow_nonneg t.property.le _)]
      rfl
    _ = _ := integral_subtype_comap measurableSet_Ioi (fun t : ℝ => t ^ k * f t)

theorem integrable_radial_integral (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ} (hf : Integrable f μ) :
    Integrable (fun θ : Metric.sphere (0 : E) 1 =>
      ∫ t in Ioi (0 : ℝ), t ^ (Module.finrank ℝ E - 1) * f (t • (θ : E)))
      μ.toSphere := by
  convert (integrable_polar_comp μ hf).integral_prod_left using 1
  ext θ
  exact (integral_volumeIoiPow_eq _ (fun t => f (t • (θ : E)))).symm

theorem ae_integrable_radial (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ} (hf : Integrable f μ) :
    ∀ᵐ θ : Metric.sphere (0 : E) 1 ∂μ.toSphere,
      IntegrableOn (fun t : ℝ => t ^ (Module.finrank ℝ E - 1) * f (t • (θ : E)))
        (Ioi (0 : ℝ)) := by
  have hi := (integrable_polar_comp μ hf).prod_right_ae
  filter_upwards [hi] with θ hθ
  let k := Module.finrank ℝ E - 1
  have hm : Measurable (fun t : Ioi (0 : ℝ) => ENNReal.ofReal ((t : ℝ) ^ k)) := by
    fun_prop
  have hcoe (t : Ioi (0 : ℝ)) :
      ((ENNReal.ofReal ((t : ℝ) ^ k)).toNNReal : ℝ) = (t : ℝ) ^ k := by
    change (ENNReal.ofReal _).toReal = _
    exact ENNReal.toReal_ofReal (pow_nonneg t.property.le _)
  have h := integrable_withDensity_iff_integrable_smul
    (μ := Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume)
    (g := fun t : Ioi (0 : ℝ) => f ((t : ℝ) • (θ : E))) hm.ennreal_toNNReal
  have hi' : Integrable
      (fun t : Ioi (0 : ℝ) => (t : ℝ) ^ k * f ((t : ℝ) • (θ : E)))
      (Measure.comap Subtype.val volume) := by
    apply (show Integrable _ (Measure.volumeIoiPow k) ↔ _ from ?_).mp hθ
    simpa [Measure.volumeIoiPow, ENNReal.coe_toNNReal, NNReal.smul_def, hcoe] using h
  exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mpr hi'

theorem ae_integrable_radial_ball (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ} {r : ℝ} (hf : IntegrableOn f (Metric.ball 0 r) μ) :
    ∀ᵐ θ : Metric.sphere (0 : E) 1 ∂μ.toSphere,
      IntegrableOn (fun t : ℝ => t ^ (Module.finrank ℝ E - 1) * f (t • (θ : E)))
        (Ioo (0 : ℝ) r) := by
  have hi := ae_integrable_radial μ ((integrable_indicator_iff measurableSet_ball).mpr hf)
  filter_upwards [hi] with θ hθ
  have hsub : Ioo (0 : ℝ) r ⊆ Ioi (0 : ℝ) := fun _ ht => ht.1
  apply (integrableOn_congr_fun ?_ measurableSet_Ioo).mp (hθ.mono_set hsub)
  intro t ht
  have hnorm : ‖t • (θ : E)‖ = t := by
    rw [norm_smul, mem_sphere_zero_iff_norm.mp θ.property, mul_one,
      Real.norm_of_nonneg ht.1.le]
  dsimp only
  rw [indicator_of_mem (show t • (θ : E) ∈ Metric.ball (0 : E) r by
    simpa only [Metric.mem_ball, dist_zero_right, hnorm] using ht.2)]

theorem integrable_radial_integral_ball (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ} {r : ℝ} (hf : IntegrableOn f (Metric.ball 0 r) μ) :
    Integrable (fun θ : Metric.sphere (0 : E) 1 =>
      ∫ t in Ioo (0 : ℝ) r, t ^ (Module.finrank ℝ E - 1) * f (t • (θ : E)))
      μ.toSphere := by
  have hi := integrable_radial_integral μ
    ((integrable_indicator_iff measurableSet_ball).mpr hf)
  apply hi.congr
  filter_upwards [] with θ
  have hθ : ‖(θ : E)‖ = 1 := mem_sphere_zero_iff_norm.1 θ.2
  rw [← integral_indicator measurableSet_Ioo,
    ← integral_indicator (measurableSet_Ioi (a := (0 : ℝ)))]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have htpos : 0 < t := ht
    have hnorm : ‖t • (θ : E)‖ = t := by
      rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_pos ht]
    by_cases htr : t < r
    · have hmem : t • (θ : E) ∈ Metric.ball (0 : E) r := by
        simpa [Metric.mem_ball, dist_eq_norm, hnorm] using htr
      simp [ht, htr, htpos, hmem, mem_Ioo]
    · have hmem : t • (θ : E) ∉ Metric.ball (0 : E) r := by
        simpa [Metric.mem_ball, dist_eq_norm, hnorm] using htr
      simp [ht, htr, hmem, mem_Ioo]
  · have hnot : t ∉ Ioo (0 : ℝ) r := fun h => ht h.1
    simp [ht, hnot]

theorem ae_polar_comp (μ : Measure E) [μ.IsAddHaarMeasure]
    {P : E → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ)
      ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)),
      P ((p.2 : ℝ) • (p.1 : E)) := by
  rw [← μ.measurePreserving_homeomorphUnitSphereProd.map_eq,
    (Homeomorph.measurableEmbedding _).ae_map_iff]
  have hms : MeasurableSet ({0}ᶜ : Set E) := (measurableSet_singleton (0 : E)).compl
  have hi := (ae_restrict_iff_subtype hms).mp (ae_restrict_of_ae hP)
  filter_upwards [hi] with x hx
  have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.2 x.2
  simpa [smul_smul, mul_inv_cancel₀ hn] using hx

theorem ae_ae_polar (μ : Measure E) [μ.IsAddHaarMeasure]
    {P : E → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ θ : Metric.sphere (0 : E) 1 ∂μ.toSphere,
      ∀ᵐ t : ℝ, 0 < t → P (t • (θ : E)) := by
  have hp := Measure.ae_ae_of_ae_prod (ae_polar_comp μ hP)
  filter_upwards [hp] with θ hθ
  have hdens : Measurable (fun t : Ioi (0 : ℝ) =>
      ENNReal.ofReal ((t : ℝ) ^ (Module.finrank ℝ E - 1))) := by fun_prop
  rw [Measure.volumeIoiPow, ae_withDensity_iff hdens] at hθ
  have hi : ∀ᵐ t : Ioi (0 : ℝ) ∂Measure.comap Subtype.val volume,
      P ((t : ℝ) • (θ : E)) := by
    filter_upwards [hθ] with t ht
    exact ht (ENNReal.ofReal_pos.mpr (pow_pos t.property _)).ne'
  exact (ae_restrict_iff' measurableSet_Ioi).mp
    ((ae_restrict_iff_subtype measurableSet_Ioi).mpr hi)

end Poincare.VolumeComparison

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem integrable_polar_integral_image_inter_ball
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {U s : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s)
    (r : ℝ) {F : M → ℝ}
    (hF : IntegrableOn F (f '' (s ∩ Metric.ball 0 r)) g.volumeMeasure) :
    Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ∫ t in Ioo (0 : ℝ) r, t ^ (n - 1) *
        s.indicator (fun x => F (f x) * g.pullbackVolumeDensity f x)
          (t • (θ : EuclideanSpace ℝ (Fin n)))) volume.toSphere := by
  have hsd : MeasurableSet (s ∩ Metric.ball 0 r) :=
    hs.inter Metric.isOpen_ball.measurableSet
  have hFi := (g.integrableOn_image_iff_pullbackDensity hU hf hsd
    (inter_subset_left.trans hsU) (hinj.mono inter_subset_left) F).mp hF
  have hind : IntegrableOn
      (s.indicator (fun x => F (f x) * g.pullbackVolumeDensity f x))
      (Metric.ball 0 r) := by
    rw [IntegrableOn, integrable_indicator_iff hs, IntegrableOn,
      Measure.restrict_restrict hs]
    exact hFi
  simpa only [finrank_euclideanSpace_fin] using
    Poincare.VolumeComparison.integrable_radial_integral_ball volume hind

theorem ae_pullback_of_ae_image
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {U s : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s)
    {P : M → Prop} (hP : ∀ᵐ y ∂g.volumeMeasure.restrict (f '' s), P y) :
    ∀ᵐ x, x ∈ s → g.pullbackVolumeDensity f x ≠ 0 → P (f x) := by
  have hemb := ContinuousOn.measurableEmbedding hs (hf.continuousOn.mono hsU) hinj
  rw [← g.map_pullbackDensity_eq_restrict_image hU hf hs hsU hinj,
    hemb.ae_map_iff] at hP
  have hρ : ContinuousOn (g.pullbackVolumeDensity f) s := fun x hx =>
    (g.continuousAt_pullbackVolumeDensity_of_contMDiffAt
      (hf.contMDiffAt (hU.mem_nhds (hsU hx)))).continuousWithinAt
  have hρm := (ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable
    (μ := volume) hs
  change AEMeasurable (fun x => ENNReal.ofReal (g.pullbackVolumeDensity f x))
    (volume.restrict s) at hρm
  have hp := (ae_restrict_iff_subtype (p := fun x => P (f x)) hs).mpr hP
  rw [restrict_withDensity hs, ae_withDensity_iff' hρm, ae_restrict_iff' hs] at hp
  filter_upwards [hp] with x hx hxs hne
  apply hx hxs
  exact (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (Real.sqrt_nonneg _) hne.symm)).ne'

theorem ae_ae_polar_of_ae_image_inter_ball
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {U s : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s)
    (r : ℝ) {P : M → Prop}
    (hP : ∀ᵐ y ∂g.volumeMeasure.restrict (f '' (s ∩ Metric.ball 0 r)), P y) :
    ∀ᵐ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∂volume.toSphere,
      ∀ᵐ t : ℝ ∂volume.restrict (Ioo (0 : ℝ) r),
        s.indicator (g.pullbackVolumeDensity f) (t • (θ : EuclideanSpace ℝ (Fin n))) ≠ 0 →
          P (f (t • (θ : EuclideanSpace ℝ (Fin n)))) := by
  have hsd : MeasurableSet (s ∩ Metric.ball 0 r) :=
    hs.inter Metric.isOpen_ball.measurableSet
  have hp := g.ae_pullback_of_ae_image hU hf hsd
    (inter_subset_left.trans hsU) (hinj.mono inter_subset_left) hP
  have hpolar := Poincare.VolumeComparison.ae_ae_polar volume hp
  filter_upwards [hpolar] with θ hθ
  filter_upwards [ae_restrict_of_ae hθ, ae_restrict_mem measurableSet_Ioo] with t ht htr
  intro hne
  have hts : t • (θ : EuclideanSpace ℝ (Fin n)) ∈ s := by
    by_contra h
    simp only [indicator_of_notMem h, ne_eq, not_true_eq_false] at hne
  have hnorm : ‖t • (θ : EuclideanSpace ℝ (Fin n))‖ = t := by
    rw [norm_smul, mem_sphere_zero_iff_norm.mp θ.property, mul_one,
      Real.norm_of_nonneg htr.1.le]
  apply ht htr.1 ⟨hts, ?_⟩
  · simpa only [indicator_of_mem hts] using hne
  · simpa only [Metric.mem_ball, dist_zero_right, hnorm] using htr.2

end PoincareConjecture.RiemannianMetric

namespace Poincare.VolumeComparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] in
private theorem measurableSet_nonterminal
    (g : PoincareConjecture.RiemannianMetric n M) (p : M) {R : ℝ}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R)) :
    MeasurableSet (localMinimizingSet (fun v => g.edist p (e v)) R \
      terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hS : MeasurableSet (localMinimizingSet (fun v => g.edist p (e v)) R) := by
    apply measurableSet_localMinimizingSet
    change ContinuousOn (fun v => EDist.edist p (e v)) (Metric.ball 0 R)
    exact continuous_edist.continuousOn.comp
      (continuous_const.continuousOn.prodMk he.continuousOn)
      (fun _ _ => Set.mem_univ _)
  exact hS.diff (measurableSet_terminalRadialPoints hS)

theorem integrable_polar_integral_ball_of_injOn
    (g : PoincareConjecture.RiemannianMetric n M) (p : M)
    {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hcover : e '' localMinimizingSet (fun v => g.edist p (e v)) R = g.ball p R)
    (hcut : g.volumeMeasure (e '' terminalRadialPoints
      (localMinimizingSet (fun v => g.edist p (e v)) R) R) = 0)
    (hinj : InjOn e
      (localMinimizingSet (fun v => g.edist p (e v)) R \
        terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R))
    {F : M → ℝ} (hF : IntegrableOn F (g.ball p r) g.volumeMeasure) :
    Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ∫ t in Ioo (0 : ℝ) r, t ^ (n - 1) *
        (localMinimizingSet (fun v => g.edist p (e v)) R \
          terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R).indicator
          (fun x => F (e x) * g.pullbackVolumeDensity e x)
          (t • (θ : EuclideanSpace ℝ (Fin n)))) volume.toSphere := by
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  have heq := ae_ball_eq_image_sdiff_terminal g p hcover hcut hr hrR
  have hFi : IntegrableOn F (e '' ((S \ T) ∩ Metric.ball 0 r)) g.volumeMeasure := by
    simpa only [IntegrableOn, Measure.restrict_congr_set heq] using hF
  exact g.integrable_polar_integral_image_inter_ball Metric.isOpen_ball he
    (measurableSet_nonterminal g p he) (fun _ hx => hx.1.1) hinj r hFi

theorem ae_integrable_polar_ball_of_injOn
    (g : PoincareConjecture.RiemannianMetric n M) (p : M)
    {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hcover : e '' localMinimizingSet (fun v => g.edist p (e v)) R = g.ball p R)
    (hcut : g.volumeMeasure (e '' terminalRadialPoints
      (localMinimizingSet (fun v => g.edist p (e v)) R) R) = 0)
    (hinj : InjOn e
      (localMinimizingSet (fun v => g.edist p (e v)) R \
        terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R))
    {F : M → ℝ} (hF : IntegrableOn F (g.ball p r) g.volumeMeasure) :
    ∀ᵐ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∂volume.toSphere,
      IntegrableOn (fun t : ℝ => t ^ (n - 1) *
        (localMinimizingSet (fun v => g.edist p (e v)) R \
          terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R).indicator
          (fun x => F (e x) * g.pullbackVolumeDensity e x)
          (t • (θ : EuclideanSpace ℝ (Fin n)))) (Ioo (0 : ℝ) r) := by
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  have heq := ae_ball_eq_image_sdiff_terminal g p hcover hcut hr hrR
  have hFi : IntegrableOn F (e '' ((S \ T) ∩ Metric.ball 0 r)) g.volumeMeasure := by
    simpa only [IntegrableOn, Measure.restrict_congr_set heq] using hF
  have hSD : MeasurableSet (S \ T) := measurableSet_nonterminal g p he
  have hSDball : MeasurableSet ((S \ T) ∩ Metric.ball 0 r) :=
    hSD.inter Metric.isOpen_ball.measurableSet
  have hsmall : (S \ T) ∩ Metric.ball 0 r ⊆ Metric.ball 0 R := fun _ hx => hx.1.1.1
  have hwi := (g.integrableOn_image_iff_pullbackDensity Metric.isOpen_ball he hSDball
    hsmall (hinj.mono inter_subset_left) F).mp hFi
  have hind : IntegrableOn
      ((S \ T).indicator (fun x => F (e x) * g.pullbackVolumeDensity e x))
      (Metric.ball 0 r) := by
    rw [IntegrableOn, integrable_indicator_iff hSD, IntegrableOn,
      Measure.restrict_restrict hSD]
    exact hwi
  simpa only [finrank_euclideanSpace_fin] using ae_integrable_radial_ball volume hind

theorem ae_ae_polar_of_ae_ball_of_injOn
    (g : PoincareConjecture.RiemannianMetric n M) (p : M)
    {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hcover : e '' localMinimizingSet (fun v => g.edist p (e v)) R = g.ball p R)
    (hcut : g.volumeMeasure (e '' terminalRadialPoints
      (localMinimizingSet (fun v => g.edist p (e v)) R) R) = 0)
    (hinj : InjOn e
      (localMinimizingSet (fun v => g.edist p (e v)) R \
        terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R))
    {P : M → Prop} (hP : ∀ᵐ y ∂g.volumeMeasure.restrict (g.ball p r), P y) :
    ∀ᵐ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∂volume.toSphere,
      ∀ᵐ t : ℝ ∂volume.restrict (Ioo (0 : ℝ) r),
        (localMinimizingSet (fun v => g.edist p (e v)) R \
          terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R).indicator
          (g.pullbackVolumeDensity e) (t • (θ : EuclideanSpace ℝ (Fin n))) ≠ 0 →
            P (e (t • (θ : EuclideanSpace ℝ (Fin n)))) := by
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  have heq := ae_ball_eq_image_sdiff_terminal g p hcover hcut hr hrR
  have hPi : ∀ᵐ y ∂g.volumeMeasure.restrict (e '' ((S \ T) ∩ Metric.ball 0 r)), P y := by
    simpa only [Measure.restrict_congr_set heq] using hP
  exact g.ae_ae_polar_of_ae_image_inter_ball Metric.isOpen_ball he
    (measurableSet_nonterminal g p he) (fun _ hx => hx.1.1) hinj r hPi

end Poincare.VolumeComparison
