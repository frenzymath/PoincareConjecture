import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.CurvatureDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology Matrix

namespace PoincareConjecture.RiemannianMetric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

noncomputable def planarVolumeDensity (g : RiemannianMetric 2 S)
    (f : ℝ × ℝ → S) (p : ℝ × ℝ) : ℝ :=
  let u := mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p (1, 0)
  let v := mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p (0, 1)
  Real.sqrt (g.inner (f p) u u * g.inner (f p) v v - (g.inner (f p) u v) ^ 2)

theorem planarVolumeDensity_nonneg (g : RiemannianMetric 2 S)
    (f : ℝ × ℝ → S) (p : ℝ × ℝ) : 0 ≤ g.planarVolumeDensity f p :=
  Real.sqrt_nonneg _

theorem planarVolumeDensity_eq_abs_frameDet (g : RiemannianMetric 2 S)
    (f : ℝ × ℝ → S) (p : ℝ × ℝ) (e₁ e₂ : TangentSpace (𝓡 2) (f p))
    (he₁ : g.inner (f p) e₁ e₁ = 1) (he₂ : g.inner (f p) e₂ e₂ = 1)
    (horth : g.inner (f p) e₁ e₂ = 0) :
    g.planarVolumeDensity f p =
      let u := mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p (1, 0)
      let v := mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p (0, 1)
      |g.inner (f p) u e₁ * g.inner (f p) v e₂ -
        g.inner (f p) u e₂ * g.inner (f p) v e₁| := by
  have h := congrArg Real.sqrt (LeviCivitaData.gramDet_eq_frameDet_sq g (f p)
    he₁ he₂ horth (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p (1, 0))
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p (0, 1)))
  rw [Real.sqrt_sq_eq_abs] at h
  exact h

private noncomputable def planeEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

private theorem measurePreserving_planeEquiv : MeasurePreserving planeEquiv := by
  exact (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

private theorem pullbackVolumeDensity_planeEquiv
    (g : RiemannianMetric 2 S) {f : ℝ × ℝ → S} {x : EuclideanSpace ℝ (Fin 2)}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f (planeEquiv x)) :
    g.pullbackVolumeDensity (f ∘ planeEquiv) x =
      g.planarVolumeDensity f (planeEquiv x) := by
  have hd := mfderiv_comp x hf planeEquiv.differentiableAt.mdifferentiableAt
  have hv (w : EuclideanSpace ℝ (Fin 2)) :
      mfderiv (𝓡 2) (𝓡 2) (f ∘ planeEquiv) x w =
        mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f (planeEquiv x) (planeEquiv w) := by
    have h := congrArg (fun L => L w) hd
    simp only [mfderiv_eq_fderiv, planeEquiv.fderiv] at h
    exact h
  have h₀ : planeEquiv (EuclideanSpace.basisFun (Fin 2) ℝ 0) = (1, 0) := by
    ext <;> simp [planeEquiv, EuclideanSpace.basisFun_apply, EuclideanSpace.single]
  have h₁ : planeEquiv (EuclideanSpace.basisFun (Fin 2) ℝ 1) = (0, 1) := by
    ext <;> simp [planeEquiv, EuclideanSpace.basisFun_apply, EuclideanSpace.single]
  unfold pullbackVolumeDensity planarVolumeDensity
  simp only [Matrix.det_fin_two, Matrix.of_apply, Function.comp_apply]
  dsimp only [TangentSpace] at *
  rw [hv, hv, h₀, h₁]
  let p := planeEquiv x
  let u := mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p (1, 0)
  let v := mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p (0, 1)
  change Real.sqrt (g.inner (f p) u u * g.inner (f p) v v -
    g.inner (f p) u v * g.inner (f p) v u) =
    Real.sqrt (g.inner (f p) u u * g.inner (f p) v v - (g.inner (f p) u v) ^ 2)
  rw [g.symm (f p) v u]
  simp only [pow_two]

theorem continuousOn_planarVolumeDensity
    (g : RiemannianMetric 2 S) (f : OpenPartialHomeomorph (ℝ × ℝ) S)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f f.source)
    (hfi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ f.symm f.target) :
    ContinuousOn (g.planarVolumeDensity f) f.source := by
  let e := planeEquiv.toHomeomorph.toOpenPartialHomeomorph.trans f
  have hes : e.source = planeEquiv ⁻¹' f.source := by simp [e]
  have het : e.target = f.target := by simp [e]
  have he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source := by
    change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (f ∘ planeEquiv) e.source
    exact hf.comp planeEquiv.contDiff.contMDiff.contMDiffOn (by
      intro x hx
      exact hes ▸ hx)
  have hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target := by
    change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (planeEquiv.symm ∘ f.symm) e.target
    rw [het]
    exact planeEquiv.symm.contDiff.contMDiff.comp_contMDiffOn hfi
  have hD : e.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt
  apply (hρ.comp planeEquiv.symm.continuous.continuousOn (by
    intro p hp
    simpa [hes] using hp)).congr
  intro p hp
  have h := pullbackVolumeDensity_planeEquiv g (x := planeEquiv.symm p)
    (by simpa using ((hf.contMDiffAt (f.open_source.mem_nhds hp)).mdifferentiableAt
      (by simp)))
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

variable [MeasurableSpace S] [BorelSpace S] [T3Space S]

theorem volumeMeasure_image_eq_lintegral_planar_gramDensity
    (g : RiemannianMetric 2 S) (f : OpenPartialHomeomorph (ℝ × ℝ) S)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f f.source)
    (hfi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ f.symm f.target)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsf : s ⊆ f.source) :
    g.volumeMeasure (f '' s) =
      ∫⁻ p in s, ENNReal.ofReal (g.planarVolumeDensity f p) := by
  let e := planeEquiv.toHomeomorph.toOpenPartialHomeomorph.trans f
  have hes : e.source = planeEquiv ⁻¹' f.source := by
    simp [e]
  have het : e.target = f.target := by
    simp [e]
  have he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source := by
    change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (f ∘ planeEquiv) e.source
    exact hf.comp planeEquiv.contDiff.contMDiff.contMDiffOn (by
      intro x hx
      exact hes ▸ hx)
  have hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target := by
    change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (planeEquiv.symm ∘ f.symm) e.target
    rw [het]
    exact planeEquiv.symm.contDiff.contMDiff.comp_contMDiffOn hfi
  have hpre : MeasurableSet (planeEquiv ⁻¹' s) := hs.preimage planeEquiv.continuous.measurable
  have hsub : planeEquiv ⁻¹' s ⊆ e.source := by
    rw [hes]
    exact preimage_mono hsf
  have himg : e '' (planeEquiv ⁻¹' s) = f '' s := by
    change (f ∘ planeEquiv) '' (planeEquiv ⁻¹' s) = _
    rw [image_comp, image_preimage_eq _ planeEquiv.surjective]
  rw [← himg, g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e he hei hpre hsub]
  calc
    _ = ∫⁻ x in planeEquiv ⁻¹' s,
        ENNReal.ofReal (g.planarVolumeDensity f (planeEquiv x)) := by
      apply setLIntegral_congr_fun hpre
      intro x hx
      exact congrArg ENNReal.ofReal (pullbackVolumeDensity_planeEquiv g
        ((hf.contMDiffAt (f.open_source.mem_nhds (hsf hx))).mdifferentiableAt (by simp)))
    _ = _ := by
      convert measurePreserving_planeEquiv.setLIntegral_comp_preimage_emb
        planeEquiv.toHomeomorph.measurableEmbedding
        (fun p => ENNReal.ofReal (g.planarVolumeDensity f p)) s using 1

theorem map_restrict_volumeMeasure_planar_symm
    (g : RiemannianMetric 2 S) (f : OpenPartialHomeomorph (ℝ × ℝ) S)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f f.source)
    (hfi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ f.symm f.target) :
    ((g.volumeMeasure.restrict f.target).map f.symm) =
      (volume.withDensity (fun p => ENNReal.ofReal (g.planarVolumeDensity f p))).restrict
        f.source := by
  ext s hs
  have hm : AEMeasurable f.symm (g.volumeMeasure.restrict f.target) :=
    f.symm.continuousOn.aemeasurable f.open_target.measurableSet
  have hset : f.symm ⁻¹' s ∩ f.target = f '' (s ∩ f.source) := by
    ext y
    constructor
    · intro hy
      exact ⟨f.symm y, ⟨hy.1, f.map_target hy.2⟩, f.right_inv hy.2⟩
    · rintro ⟨x, ⟨hxs, hxf⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, f.left_inv hxf], f.map_source hxf⟩
  rw [Measure.map_apply_of_aemeasurable hm hs,
    Measure.restrict_apply' f.open_target.measurableSet, hset,
    g.volumeMeasure_image_eq_lintegral_planar_gramDensity f hf hfi
      (hs.inter f.open_source.measurableSet) inter_subset_right,
    Measure.restrict_apply hs, withDensity_apply _ (hs.inter f.open_source.measurableSet)]

theorem integral_image_eq_integral_planar_density
    (g : RiemannianMetric 2 S) (f : OpenPartialHomeomorph (ℝ × ℝ) S)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f f.source)
    (hfi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ f.symm f.target)
    {H : S → ℝ} (hH : ContinuousOn H f.target)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsf : s ⊆ f.source) :
    (∫ x in f '' s, H x ∂g.volumeMeasure) =
      ∫ p in s, H (f p) * g.planarVolumeDensity f p := by
  have hmap := g.map_restrict_volumeMeasure_planar_symm f hf hfi
  have hc : ContinuousOn (fun p => H (f p)) f.source :=
    hH.comp f.continuousOn f.mapsTo
  have hm : AEStronglyMeasurable (fun p => H (f p))
      ((g.volumeMeasure.restrict f.target).map f.symm) := by
    rw [hmap]
    exact hc.aestronglyMeasurable f.open_source.measurableSet
  have hi := setIntegral_map hs hm
    (f.symm.continuousOn.aemeasurable f.open_target.measurableSet)
  have hset : f.symm ⁻¹' s ∩ f.target = f '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨f.symm x, hx.1, f.right_inv hx.2⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨by simpa only [mem_preimage, f.left_inv (hsf hp)], f.map_source (hsf hp)⟩
  rw [hmap, Measure.restrict_restrict_of_subset hsf,
    Measure.restrict_restrict' f.open_target.measurableSet, hset] at hi
  have hid : (∫ x in f '' s, H (f (f.symm x)) ∂g.volumeMeasure) =
      ∫ x in f '' s, H x ∂g.volumeMeasure := by
    apply integral_congr_ae
    apply ae_restrict_of_ae_restrict_of_subset (image_subset_iff.mpr
      (fun p hp => f.map_source (hsf hp)))
    filter_upwards [ae_restrict_mem f.open_target.measurableSet] with x hx
    rw [f.right_inv hx]
  rw [hid] at hi
  rw [← hi]
  have hwith := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (μ := volume) (f := fun p => ENNReal.ofReal (g.planarVolumeDensity f p)) (s := s)
    ((ENNReal.continuous_ofReal.comp_continuousOn
      ((g.continuousOn_planarVolumeDensity f hf hfi).mono hsf)).aemeasurable hs)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun p => H (f p)) hs
  rw [hwith]
  apply setIntegral_congr_fun hs
  intro p hp
  simp only [ENNReal.toReal_ofReal (g.planarVolumeDensity_nonneg f p), smul_eq_mul, mul_comm]

theorem integral_target_eq_integral_planar_density
    (g : RiemannianMetric 2 S) (f : OpenPartialHomeomorph (ℝ × ℝ) S)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f f.source)
    (hfi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ f.symm f.target)
    {H : S → ℝ} (hH : ContinuousOn H f.target) :
    (∫ x in f.target, H x ∂g.volumeMeasure) =
      ∫ p in f.source, H (f p) * g.planarVolumeDensity f p := by
  simpa only [f.image_source_eq_target] using
    g.integral_image_eq_integral_planar_density f hf hfi hH
      f.open_source.measurableSet Subset.rfl

end PoincareConjecture.RiemannianMetric
