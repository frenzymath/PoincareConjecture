import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Lipschitz








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem integrableOn_integral_pullback_density
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {F : M → ℝ} (hF : IntegrableOn F e.target g.volumeMeasure) :
    IntegrableOn (fun x => F (e x) * g.pullbackVolumeDensity e x) e.source ∧
      (∫ x in e.target, F x ∂g.volumeMeasure) =
        ∫ x in e.source, F (e x) * g.pullbackVolumeDensity e x := by
  let μ := g.volumeMeasure.restrict e.target
  let ν := (volume.restrict e.source).withDensity
    (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt
  have hd : AEMeasurable (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
      (volume.restrict e.source) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable e.open_source.measurableSet
  have hmapSymm : μ.map e.symm = ν := by
    dsimp [μ, ν]
    rw [g.map_restrict_volumeMeasure_symm e he hei,
      restrict_withDensity e.open_source.measurableSet]
  have hmeas : AEMeasurable e ν :=
    (e.continuousOn.aemeasurable e.open_source.measurableSet).mono'
      (withDensity_absolutelyContinuous _ _)
  have hmap : ν.map e = μ := by
    rw [← hmapSymm, AEMeasurable.map_map_of_aemeasurable]
    · calc
        μ.map (e ∘ e.symm) = μ.map id := Measure.map_congr (by
          filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
          exact e.right_inv hy)
        _ = μ := Measure.map_id
    · rw [hmapSymm]
      exact hmeas
    · exact e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  have hFmap : Integrable F (ν.map e) := by
    rw [hmap]
    exact hF
  have hcomp : Integrable (fun x => F (e x)) ν := hFmap.comp_aemeasurable hmeas
  have hnonneg (x) : 0 ≤ g.pullbackVolumeDensity e x := Real.sqrt_nonneg _
  constructor
  · have hi := (integrable_withDensity_iff_integrable_smul₀' hd (by simp)).1 hcomp
    simpa only [IntegrableOn, ENNReal.toReal_ofReal (hnonneg _),
      smul_eq_mul, mul_comm] using hi
  · change (∫ x, F x ∂μ) = _
    rw [← hmap, integral_map hmeas hFmap.aestronglyMeasurable]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hd (by simp)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul, mul_comm]

end PoincareConjecture.RiemannianMetric
