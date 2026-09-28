import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.GaussianWeight
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.PositivePart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.VolumeSupport










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

open Poincare.Analysis.Heat

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}



theorem karpLi_nonpos_of_short_time (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M) {u : ℝ × M → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hshort : b ≤ 1 / (32 * a))
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioo 0 b ×ˢ univ))
    (huc : ContinuousOn u (Icc 0 b ×ˢ univ))
    (hsub : ∀ t ∈ Ioo 0 b, ∀ x,
      deriv (fun s ↦ u (s, x)) t ≤ D.laplacian (fun y ↦ u (t, y)) x)
    (hzero : ∀ x, u (0, x) ≤ 0)
    (hi : Integrable (fun p : ℝ × M ↦ Real.exp (-a * (g.edist O p.2).toReal ^ 2) *
      max (u p) 0 ^ 2) ((volume.restrict (Ioc 0 b)).prod g.volumeMeasure)) :
    ∀ x, u (b, x) ≤ 0 := by
  obtain ⟨ρ, hρ, hρdist, hρgrad⟩ := D.exists_smooth_distance_majorant O
  let ξ : ℝ × M → ℝ := fun p ↦ -(ρ p.2 ^ 2) / (16 * (2 * b - p.1))
  let v : ℝ × M → ℝ := fun p ↦ smoothPositivePart (u p)
  have hvc : ContinuousOn v (Icc 0 b ×ˢ univ) :=
    contDiff_smoothPositivePart.continuous.comp_continuousOn huc
  have hξc : ContinuousOn ξ (Icc 0 b ×ˢ univ) :=
    continuousOn_gaussian_weight hρ hb le_rfl
  have hξ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ ξ (Ioo 0 b ×ˢ univ) := by
    apply (contMDiffOn_gaussian_weight hρ b).mono
    intro p hp
    refine ⟨?_, mem_univ _⟩
    change p.1 < 2 * b
    have := hp.1.2
    linarith
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ v (Ioo 0 b ×ˢ univ) :=
    contDiff_smoothPositivePart.contMDiff.comp_contMDiffOn hu
  have hvi : Integrable (fun p : ℝ × M ↦ Real.exp (ξ p) * v p ^ 2)
      ((volume.restrict (Ioc 0 b)).prod g.volumeMeasure) := by
    apply hi.mono' ?_ ?_
    · have hm := ((Real.continuous_exp.comp_continuousOn hξc).mul (hvc.pow 2)).aemeasurable
        (μ := volume.prod g.volumeMeasure) (measurableSet_Icc.prod MeasurableSet.univ)
      have hm' := hm.mono_set (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)
      rw [← Measure.prod_restrict, Measure.restrict_univ] at hm'
      exact hm'.aestronglyMeasurable
    · have ht : ∀ᵐ p : ℝ × M ∂(volume.restrict (Ioc 0 b)).prod g.volumeMeasure,
          p.1 ∈ Ioc 0 b :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
      filter_upwards [ht] with p hp
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (ξ p) * v p ^ 2)]
      apply mul_le_mul
      · exact exp_gaussian_weight_le ENNReal.toReal_nonneg (hρdist p.2)
          hb ha hshort hp.1.le hp.2
      · apply (sq_le_sq₀ (smoothPositivePart_nonneg _) (le_max_right _ _)).mpr
        exact smoothPositivePart_le_posPart _
      · exact sq_nonneg _
      · exact (Real.exp_pos _).le
  have hz := D.weighted_subsolution_ae_eq_zero hcomplete O hb.le isOpen_Ioo Subset.rfl
    hv hξ hvc hξc (fun _ _ _ ↦ smoothPositivePart_nonneg _) ?_ ?_ ?_ hvi
  · have hvb : Continuous (fun x ↦ v (b, x)) :=
      hvc.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x ↦ ⟨⟨hb.le, le_rfl⟩, mem_univ x⟩)
    have he := Measure.eq_of_ae_eq hz hvb continuous_const
    intro x
    exact (smoothPositivePart_eq_zero_iff _).mp (congrFun he x)
  · intro t ht x
    have hgu (y : M) : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (t, y) :=
      hu.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ y⟩)
    exact D.smoothPositivePart_subsolution x
      (fun y ↦ (hgu y).comp y (contMDiffAt_const.prodMk contMDiffAt_id))
      (((hgu x).comp t (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt.differentiableAt
        (by simp)) (hsub t ht x)
  · intro t ht x
    exact D.gaussian_weight_differential_inequality hρ hρgrad (by
      have := ht.2
      linarith) x
  · intro x
    exact smoothPositivePart_eq_zero_of_nonpos (hzero x)


theorem karpLi_nonpos_on_short_interval (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M) {u : ℝ × M → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hshort : b ≤ 1 / (32 * a))
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioo 0 b ×ˢ univ))
    (huc : ContinuousOn u (Icc 0 b ×ˢ univ))
    (hsub : ∀ t ∈ Ioo 0 b, ∀ x,
      deriv (fun s ↦ u (s, x)) t ≤ D.laplacian (fun y ↦ u (t, y)) x)
    (hzero : ∀ x, u (0, x) ≤ 0)
    (hi : Integrable (fun p : ℝ × M ↦ Real.exp (-a * (g.edist O p.2).toReal ^ 2) *
      max (u p) 0 ^ 2) ((volume.restrict (Ioc 0 b)).prod g.volumeMeasure)) :
    ∀ t ∈ Icc 0 b, ∀ x, u (t, x) ≤ 0 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with he | ht0
  · simpa [← he] using hzero
  · apply D.karpLi_nonpos_of_short_time hcomplete O ha ht0 (ht.2.trans hshort)
      (hu.mono (Set.prod_mono (Ioo_subset_Ioo le_rfl ht.2) Subset.rfl))
      (huc.mono (Set.prod_mono (Icc_subset_Icc le_rfl ht.2) Subset.rfl))
      (fun s hs ↦ hsub s ⟨hs.1, hs.2.trans_le ht.2⟩) hzero
    exact hi.mono_measure (Measure.prod_mono
      (Measure.restrict_mono (Ioc_subset_Ioc le_rfl ht.2) le_rfl) le_rfl)

end PoincareConjecture.LeviCivitaData
