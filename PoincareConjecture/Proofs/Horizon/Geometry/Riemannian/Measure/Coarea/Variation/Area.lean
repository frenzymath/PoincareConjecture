import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Weighted
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Proper
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.RegularDomain








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]


noncomputable def RiemannianMetric.regularLevelArea
    (g : RiemannianMetric (n + 1) M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f) (t : ℝ) : ℝ :=
  (g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t).real univ

theorem RiemannianMetric.regularLevelArea_nonneg
    (g : RiemannianMetric (n + 1) M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f) (t : ℝ) :
    0 ≤ g.regularLevelArea hf t := ENNReal.toReal_nonneg

namespace LeviCivitaData

variable {g : RiemannianMetric (n + 1) M} (D : LeviCivitaData g)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)

omit [MeasurableSpace M] [BorelSpace M] in
private theorem exists_area_cutoff {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {t : ℝ} (ht : t ∈ I) :
    ∃ χ : M → ℝ, ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ g.regularDomain hf ∧
      (∀ᶠ c in 𝓝 t, ∀ x, f x = c → χ =ᶠ[𝓝 x] 1) := by
  obtain ⟨a, b, -, htab, habI⟩ := exists_Icc_mem_subset_of_mem_nhds (hI.mem_nhds ht)
  have hK := Poincare.Coarea.isCompact_slab_of_isProperMap hproper habI
  have hKU : f ⁻¹' Icc a b ⊆ g.regularDomain hf := by
    intro x hx
    exact (g.mem_regularDomain_iff hf x).mpr (hreg x (habI hx))
  obtain ⟨χ, hχ, hχc, hχs, -, hχone⟩ :=
    exists_contMDiff_cutoff_of_isCompact (n := n + 1) hK (g.regularDomain hf).isOpen hKU
  refine ⟨χ, hχ, hχc, hχs, ?_⟩
  filter_upwards [htab] with c hc
  intro x hx
  exact hχone x (by change f x ∈ Icc a b; rwa [hx])

private theorem area_eq_integral_cutoff {χ : M → ℝ} {t : ℝ}
    (hχ : ∀ x, f x = t → χ x = 1) :
    g.regularLevelArea hf t =
      ∫ z, χ (openLevelIncl f (g.regularDomain hf) t z)
        ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t := by
  have heq : (fun z => χ (openLevelIncl f (g.regularDomain hf) t z)) = fun _ => (1 : ℝ) :=
    funext fun z => hχ _ z.2
  rw [heq, integral_const]
  simp [RiemannianMetric.regularLevelArea]

include hf in
omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
private theorem levelVariation_eq_of_one_near {χ : M → ℝ} {x : M}
    (hx : mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hχ : χ =ᶠ[𝓝 x] 1) :
    D.levelVariation f χ x = D.levelMeanCurvature f x /
      g.tangentNorm x (g.gradient f x) := by
  have hq : 0 < D.levelQ f x :=
    Real.sqrt_pos.mp ((g.tangentNorm_gradient_pos_iff f x).mpr hx)
  have hgrad : D.gradient χ x = 0 := by
    unfold gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq hχ]
    change (g.inner x).inverse (mvfderiv (𝓡 (n + 1)) (fun _ : M => (1 : ℝ)) x) = 0
    simp [mvfderiv]
  rw [D.levelVariation_eq_meanCurvature hf x hq, hgrad, hχ.eq_of_nhds]
  simp only [map_zero, zero_apply, zero_div, Pi.one_apply, one_mul, zero_add]
  rfl


theorem isFiniteMeasure_regularLevelVolume_of_isProperMap
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {t : ℝ} (ht : t ∈ I) :
    IsFiniteMeasure (g.regularLevelVolume hf (g.regularDomain hf)
      (g.regularDomain_regular hf) t) := by
  obtain ⟨χ, hχ, hχc, hχs, hχone⟩ := exists_area_cutoff hf hI hproper hreg ht
  have hi := g.integrable_regularLevelVolume_of_hasCompactSupport hf (g.regularDomain hf)
    (g.regularDomain_regular hf) t hχ.continuous hχc hχs
  have heq : (fun z => χ (openLevelIncl f (g.regularDomain hf) t z)) = fun _ => (1 : ℝ) :=
    funext fun z => (hχone.self_of_nhds _ z.2).eq_of_nhds
  change Integrable (fun z => χ (openLevelIncl f (g.regularDomain hf) t z)) _ at hi
  rw [heq] at hi
  exact (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp hi



theorem first_variation_regularLevelArea
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) :
    ContDiffOn ℝ ∞ (g.regularLevelArea hf) I ∧
      ∀ t ∈ I, HasDerivAt (g.regularLevelArea hf)
        (∫ z, D.levelMeanCurvature f
            (openLevelIncl f (g.regularDomain hf) t z) /
          g.tangentNorm (openLevelIncl f (g.regularDomain hf) t z)
            (g.gradient f (openLevelIncl f (g.regularDomain hf) t z))
          ∂g.regularLevelVolume hf (g.regularDomain hf)
            (g.regularDomain_regular hf) t) t := by
  have hlocal (t : ℝ) (ht : t ∈ I) :
      ContDiffAt ℝ ∞ (g.regularLevelArea hf) t ∧
      HasDerivAt (g.regularLevelArea hf)
        (∫ z, D.levelMeanCurvature f
            (openLevelIncl f (g.regularDomain hf) t z) /
          g.tangentNorm (openLevelIncl f (g.regularDomain hf) t z)
            (g.gradient f (openLevelIncl f (g.regularDomain hf) t z))
          ∂g.regularLevelVolume hf (g.regularDomain hf)
            (g.regularDomain_regular hf) t) t := by
    obtain ⟨χ, hχ, hχc, hχs, hχone⟩ := exists_area_cutoff hf hI hproper hreg ht
    have heq : g.regularLevelArea hf =ᶠ[𝓝 t]
        fun c => ∫ z, χ (openLevelIncl f (g.regularDomain hf) c z)
          ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) c := by
      filter_upwards [hχone] with c hc
      exact area_eq_integral_cutoff hf (fun x hx => (hc x hx).eq_of_nhds)
    refine ⟨((D.contDiff_regularLevelIntegral hf (g.regularDomain hf)
      (g.regularDomain_regular hf) hχ hχc hχs).contDiffAt).congr_of_eventuallyEq heq, ?_⟩
    have hd := (D.hasDerivAt_regularLevelIntegral hf (g.regularDomain hf)
      (g.regularDomain_regular hf) hχ hχc hχs t).congr_of_eventuallyEq heq
    apply hd.congr_deriv
    apply integral_congr_ae
    filter_upwards [] with z
    exact D.levelVariation_eq_of_one_near hf
      (g.regularDomain_regular hf _ z.1.2) (hχone.self_of_nhds _ z.2)
  exact ⟨fun t ht => (hlocal t ht).1.contDiffWithinAt, fun t ht => (hlocal t ht).2⟩

end LeviCivitaData
end PoincareConjecture
