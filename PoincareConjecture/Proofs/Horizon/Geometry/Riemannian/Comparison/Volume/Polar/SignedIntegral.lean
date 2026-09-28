import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.Density
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.Domain
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology Bundle

namespace Poincare.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem integral_eq_polar (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ} (hf : Integrable f μ) :
    (∫ x, f x ∂μ) =
      ∫ θ : Metric.sphere (0 : E) 1,
        (∫ t in Ioi (0 : ℝ),
          t ^ (Module.finrank ℝ E - 1) * f (t • (θ : E))) ∂μ.toSphere := by
  have hms : MeasurableSet ({0}ᶜ : Set E) :=
    (measurableSet_singleton (0 : E)).compl
  let F : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ :=
    fun p => f ((p.2 : ℝ) • (p.1 : E))
  have hscale (x : ({0}ᶜ : Set E)) :
      F (homeomorphUnitSphereProd E x) = f (x : E) := by
    have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.2 x.2
    simp [F, smul_smul, mul_inv_cancel₀ hn]
  have hi : Integrable (f ∘ Subtype.val) (μ.comap (Subtype.val : ({0}ᶜ : Set E) → E)) :=
    (integrableOn_iff_comap_subtypeVal hms).mp hf.integrableOn
  have hcomp : F ∘ homeomorphUnitSphereProd E = f ∘ Subtype.val := by
    funext x
    exact hscale x
  have hFi : Integrable F
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) :=
    (μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      (Homeomorph.measurableEmbedding _)).mp (by
        simpa only [hcomp] using hi)
  have hfirst : (∫ x, f x ∂μ) =
      ∫ x : ({0}ᶜ : Set E), f (x : E) ∂μ.comap Subtype.val := by
    rw [integral_subtype_comap hms, restrict_compl_singleton]
  rw [hfirst]
  calc
    (∫ x : ({0}ᶜ : Set E), f (x : E) ∂μ.comap Subtype.val) =
        ∫ p, F p ∂(μ.toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      rw [← μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) F]
      exact integral_congr_ae (Eventually.of_forall fun x => (hscale x).symm)
    _ = _ := by
      rw [integral_prod _ hFi]
      apply integral_congr_ae
      filter_upwards [] with θ
      have hdens : Measurable (fun t : Ioi (0 : ℝ) =>
          ENNReal.ofReal ((t : ℝ) ^ (Module.finrank ℝ E - 1))) := by fun_prop
      rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul hdens
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      calc
        _ = ∫ t : Ioi (0 : ℝ),
            (t : ℝ) ^ (Module.finrank ℝ E - 1) * f ((t : ℝ) • (θ : E))
              ∂Measure.comap Subtype.val volume := by
          apply integral_congr_ae
          filter_upwards [] with t
          rw [ENNReal.toReal_ofReal (pow_nonneg t.property.le _)]
          rfl
        _ = _ := integral_subtype_comap measurableSet_Ioi
          (fun t : ℝ => t ^ (Module.finrank ℝ E - 1) * f (t • (θ : E)))

theorem setIntegral_ball_eq_polar (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ} (r : ℝ) (hf : IntegrableOn f (Metric.ball 0 r) μ) :
    (∫ x in Metric.ball 0 r, f x ∂μ) =
      ∫ θ : Metric.sphere (0 : E) 1,
        (∫ t in Ioo (0 : ℝ) r,
          t ^ (Module.finrank ℝ E - 1) * f (t • (θ : E))) ∂μ.toSphere := by
  have hind := (integrable_indicator_iff measurableSet_ball).mpr hf
  rw [← integral_indicator measurableSet_ball, integral_eq_polar μ hind]
  apply integral_congr_ae
  filter_upwards [] with θ
  have hθ : ‖(θ : E)‖ = 1 := mem_sphere_zero_iff_norm.1 θ.2
  rw [← integral_indicator measurableSet_Ioo,
    ← integral_indicator (measurableSet_Ioi (a := (0 : ℝ)))]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have htpos : 0 < t := ht
    have hnorm : ‖t • (θ : E)‖ = t := by
      rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_pos htpos]
    by_cases htr : t < r
    · have hmem : t • (θ : E) ∈ Metric.ball (0 : E) r := by
        simpa [Metric.mem_ball, dist_eq_norm, hnorm] using htr
      simp [indicator_of_mem, ht, htr, htpos, hmem, mem_Ioo]
    · have hmem : t • (θ : E) ∉ Metric.ball (0 : E) r := by
        simpa [Metric.mem_ball, dist_eq_norm, hnorm] using htr
      simp [indicator_of_notMem, ht, htr, hmem, mem_Ioo]
  · have hnot : t ∉ Ioo (0 : ℝ) r := fun h => ht h.1
    simp [indicator_of_notMem, ht, hnot]

end Poincare.VolumeComparison

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem map_pullbackDensity_eq_restrict_image
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {U s : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s) :
    Measure.map (s.domRestrict f)
      (Measure.comap (Subtype.val : s → EuclideanSpace ℝ (Fin n))
        (volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity f x)))) =
      g.volumeMeasure.restrict (f '' s) := by
  have hemb := ContinuousOn.measurableEmbedding hs (hf.continuousOn.mono hsU) hinj
  have hcoe := MeasurableEmbedding.subtype_coe hs
  ext t ht
  rw [hemb.map_apply, hcoe.comap_apply, Measure.restrict_apply ht]
  have hpre : MeasurableSet
      ((Subtype.val : s → EuclideanSpace ℝ (Fin n)) '' ((s.domRestrict f) ⁻¹' t)) :=
    hcoe.measurableSet_image.mpr (hemb.measurable ht)
  rw [withDensity_apply _ hpre]
  rw [← g.volumeMeasure_image_eq_lintegral_of_mdifferentiableAt_injOn hpre
    (fun x hx => ?_) (hinj.mono (Subtype.coe_image_subset _ _))]
  · congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨hz, ⟨z, z.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  · exact (hf.contMDiffAt (hU.mem_nhds (hsU (Subtype.coe_image_subset _ _ hx)))).mdifferentiableAt
      (by simp)

theorem integral_image_eq_integral_pullbackDensity
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {U s : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s)
    (F : M → ℝ) :
    (∫ y in f '' s, F y ∂g.volumeMeasure) =
      ∫ x in s, F (f x) * g.pullbackVolumeDensity f x := by
  have hemb := ContinuousOn.measurableEmbedding hs (hf.continuousOn.mono hsU) hinj
  rw [← g.map_pullbackDensity_eq_restrict_image hU hf hs hsU hinj, hemb.integral_map]
  change (∫ x : s, F (f x) ∂Measure.comap Subtype.val
    (volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity f x)))) = _
  rw [integral_subtype_comap hs (fun x => F (f x))]
  have hρ : ContinuousOn (g.pullbackVolumeDensity f) s := fun x hx =>
    (g.continuousAt_pullbackVolumeDensity_of_contMDiffAt
      (hf.contMDiffAt (hU.mem_nhds (hsU hx)))).continuousWithinAt
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (μ := volume) (f := fun x => ENNReal.ofReal (g.pullbackVolumeDensity f x))
    ((ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable hs)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun x => F (f x)) hs]
  apply setIntegral_congr_fun hs
  intro x _
  simp [pullbackVolumeDensity, ENNReal.toReal_ofReal, Real.sqrt_nonneg,
    smul_eq_mul, mul_comm]

theorem integrableOn_image_iff_pullbackDensity
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {U s : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s)
    (F : M → ℝ) :
    IntegrableOn F (f '' s) g.volumeMeasure ↔
      IntegrableOn (fun x => F (f x) * g.pullbackVolumeDensity f x) s := by
  have hemb := ContinuousOn.measurableEmbedding hs (hf.continuousOn.mono hsU) hinj
  rw [IntegrableOn, ← g.map_pullbackDensity_eq_restrict_image hU hf hs hsU hinj,
    hemb.integrable_map_iff]
  change Integrable ((fun x => F (f x)) ∘ Subtype.val)
    (Measure.comap (Subtype.val : s → EuclideanSpace ℝ (Fin n))
      (volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity f x)))) ↔ _
  rw [← integrableOn_iff_comap_subtypeVal hs, IntegrableOn, restrict_withDensity hs]
  have hρ : ContinuousOn (g.pullbackVolumeDensity f) s := fun x hx =>
    (g.continuousAt_pullbackVolumeDensity_of_contMDiffAt
      (hf.contMDiffAt (hU.mem_nhds (hsU hx)))).continuousWithinAt
  have hm := ((ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable
    (μ := volume) hs).ennreal_toNNReal
  have h := integrable_withDensity_iff_integrable_smul₀
    (μ := volume.restrict s) (g := fun x => F (f x)) hm
  have hcoe (x : EuclideanSpace ℝ (Fin n)) :
      ((ENNReal.ofReal (g.pullbackVolumeDensity f x)).toNNReal : ℝ) =
        g.pullbackVolumeDensity f x := by
    change (ENNReal.ofReal _).toReal = _
    exact ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
  simpa [IntegrableOn, ENNReal.coe_toNNReal, NNReal.smul_def, hcoe, mul_comm] using h

theorem integral_image_inter_ball_eq_polar
    (g : RiemannianMetric n M) (hn : 1 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {U s : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s)
    (r : ℝ) {F : M → ℝ}
    (hF : IntegrableOn F (f '' (s ∩ Metric.ball 0 r)) g.volumeMeasure) :
    (∫ y in f '' (s ∩ Metric.ball 0 r), F y ∂g.volumeMeasure) =
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ t in Ioo (0 : ℝ) r, t ^ (n - 1) *
          s.indicator (fun x => F (f x) * g.pullbackVolumeDensity f x)
            (t • (θ : EuclideanSpace ℝ (Fin n)))) ∂volume.toSphere := by
  have : NeZero n := ⟨by omega⟩
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
  rw [g.integral_image_eq_integral_pullbackDensity hU hf hsd
    (inter_subset_left.trans hsU) (hinj.mono inter_subset_left)]
  have hpolar := Poincare.VolumeComparison.setIntegral_ball_eq_polar
    (volume : Measure (EuclideanSpace ℝ (Fin n))) r hind
  rw [integral_indicator hs, Measure.restrict_restrict hs] at hpolar
  simpa only [finrank_euclideanSpace_fin] using hpolar

end PoincareConjecture.RiemannianMetric

namespace Poincare.VolumeComparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem ae_ball_eq_image_sdiff_terminal
    (g : PoincareConjecture.RiemannianMetric n M) (p : M)
    {e : EuclideanSpace ℝ (Fin n) → M} {R r : ℝ}
    (hcover : e '' localMinimizingSet (fun v => g.edist p (e v)) R = g.ball p R)
    (hcut : g.volumeMeasure (e '' terminalRadialPoints
      (localMinimizingSet (fun v => g.edist p (e v)) R) R) = 0)
    (hr : 0 < r) (hrR : r ≤ R) :
    g.ball p r =ᵐ[g.volumeMeasure]
      e '' ((localMinimizingSet (fun v => g.edist p (e v)) R \
        terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R) ∩
          Metric.ball 0 r) := by
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  have himage := image_localMinimizingSet_inter_ball g p hcover hr hrR
  change e '' (S ∩ Metric.ball 0 r) = g.ball p r at himage
  have hTae : ∀ᵐ x ∂g.volumeMeasure, x ∉ e '' T := by
    apply ae_iff.mpr
    simpa only [not_not, T, S, ofPred_mem_eq] using hcut
  filter_upwards [hTae] with x hx
  apply propext
  rw [← himage]
  constructor
  · rintro ⟨v, ⟨hvS, hvr⟩, rfl⟩
    exact ⟨v, ⟨⟨hvS, fun hvT => hx ⟨v, hvT, rfl⟩⟩, hvr⟩, rfl⟩
  · rintro ⟨v, ⟨⟨hvS, _⟩, hvr⟩, rfl⟩
    exact ⟨v, ⟨hvS, hvr⟩, rfl⟩

theorem integral_ball_eq_polar_of_injOn
    (g : PoincareConjecture.RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
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
    (∫ x in g.ball p r, F x ∂g.volumeMeasure) =
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ t in Ioo (0 : ℝ) r, t ^ (n - 1) *
          (localMinimizingSet (fun v => g.edist p (e v)) R \
            terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R).indicator
            (fun x => F (e x) * g.pullbackVolumeDensity e x)
            (t • (θ : EuclideanSpace ℝ (Fin n)))) ∂volume.toSphere := by
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hS : MeasurableSet S := by
    apply measurableSet_localMinimizingSet
    change ContinuousOn (fun v => EDist.edist p (e v)) (Metric.ball 0 R)
    exact continuous_edist.continuousOn.comp
      (continuous_const.continuousOn.prodMk he.continuousOn)
      (fun _ _ => Set.mem_univ _)
  have hSD : MeasurableSet (S \ T) :=
    hS.diff (measurableSet_terminalRadialPoints hS)
  have heq := ae_ball_eq_image_sdiff_terminal g p hcover hcut hr hrR
  have hFi : IntegrableOn F (e '' ((S \ T) ∩ Metric.ball 0 r)) g.volumeMeasure := by
    simpa only [IntegrableOn, Measure.restrict_congr_set heq] using hF
  rw [setIntegral_congr_set heq]
  exact g.integral_image_inter_ball_eq_polar hn Metric.isOpen_ball he hSD
    (fun _ hx => hx.1.1) hinj r hFi

end Poincare.VolumeComparison
