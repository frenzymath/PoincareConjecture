import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.ChangeOfVariables
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem RiemannianMetric.integral_image_eq_integral_pullback_density
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    (hse : s ⊆ e.source) {f : M → ℝ} (hf : ContinuousOn f e.target) :
    (∫ y in e '' s, f y ∂g.volumeMeasure) =
      ∫ x in s, f (e x) * g.pullbackVolumeDensity e x := by
  have hmap := g.map_restrict_volumeMeasure_symm e he hei
  have hc : ContinuousOn (fun x => f (e x)) e.source :=
    hf.comp e.continuousOn e.mapsTo
  have hm : AEStronglyMeasurable (fun x => f (e x))
      ((g.volumeMeasure.restrict e.target).map e.symm) := by
    rw [hmap]
    exact hc.aestronglyMeasurable e.open_source.measurableSet
  have hi := setIntegral_map hs hm
    (e.symm.continuousOn.aemeasurable e.open_target.measurableSet)
  have hset : e.symm ⁻¹' s ∩ e.target = e '' s := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, hy.1, e.right_inv hy.2⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simpa only [mem_preimage, e.left_inv (hse hx)], e.map_source (hse hx)⟩
  have hid : (∫ y in e.symm ⁻¹' s, f (e (e.symm y))
      ∂g.volumeMeasure.restrict e.target) =
      ∫ y in e '' s, f y ∂g.volumeMeasure := by
    calc
      _ = ∫ y in e.symm ⁻¹' s, f y ∂g.volumeMeasure.restrict e.target := by
        apply integral_congr_ae
        apply ae_restrict_of_ae
        filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
        exact congrArg f (e.right_inv hy)
      _ = _ := by rw [Measure.restrict_restrict' e.open_target.measurableSet, hset]
  rw [hid, hmap, Measure.restrict_restrict hs, inter_eq_left.mpr hse] at hi
  rw [← hi]
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) s := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hse hx)))
      (hD.mfderiv_injective (hse hx))).1.continuousAt.continuousWithinAt
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (μ := volume) (f := fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
    (s := s)
    ((ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable hs)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun x => f (e x)) hs]
  apply setIntegral_congr_fun hs
  intro x hx
  simp [RiemannianMetric.pullbackVolumeDensity, Real.sqrt_nonneg,
    smul_eq_mul, mul_comm]

theorem RiemannianMetric.volumeMeasure_image_toReal_eq_integral_pullbackVolumeDensity
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    (hse : s ⊆ e.source) :
    (g.volumeMeasure (e '' s)).toReal = ∫ x in s, g.pullbackVolumeDensity e x := by
  simpa [integral_const, Measure.real, smul_eq_mul] using
    g.integral_image_eq_integral_pullback_density e he hei hs hse
      (f := fun _ => 1) continuousOn_const

theorem RicciFlow.hasDerivAt_volumeMeasure_image_of_subset
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hD : (F.connection t).CurvatureTensorCalculus)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K L : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L)
    (hLe : L ⊆ e.source) :
    HasDerivAt (fun s => ((F.metric s).volumeMeasure (e '' K)).toReal)
      (-(∫ y in e '' K, (F.connection t).scalarCurvature y
        ∂(F.metric t).volumeMeasure)) t := by
  have heD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hd := F.hasDerivAt_integral_pullbackVolumeDensity_of_subset ht hD e hK hL hKL
    (fun x hx => he.contMDiffAt (e.open_source.mem_nhds (hLe hx)))
    (fun x hx => heD.mfderiv_injective (hLe hx))
  have hfun : (fun s => ((F.metric s).volumeMeasure (e '' K)).toReal) =
      (fun s => ∫ x in K, (F.metric s).pullbackVolumeDensity e x) := by
    funext s
    exact (F.metric s).volumeMeasure_image_toReal_eq_integral_pullbackVolumeDensity
      e he hei hK (hKL.trans hLe)
  rw [hfun]
  convert hd using 1
  rw [(F.metric t).integral_image_eq_integral_pullback_density e he hei
    hK (hKL.trans hLe) hD.contMDiff_scalarCurvature.continuous.continuousOn]
  simp only [neg_mul, integral_neg]

theorem RicciFlow.hasDerivAt_volumeMeasure_image
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (hD : (F.connection t).CurvatureTensorCalculus)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKe : K ⊆ e.source) :
    HasDerivAt (fun s => ((F.metric s).volumeMeasure (e '' K)).toReal)
      (-(∫ y in e '' K, (F.connection t).scalarCurvature y
        ∂(F.metric t).volumeMeasure)) t :=
  F.hasDerivAt_volumeMeasure_image_of_subset ht hD e he hei
    hK.measurableSet hK Subset.rfl hKe

end PoincareConjecture
