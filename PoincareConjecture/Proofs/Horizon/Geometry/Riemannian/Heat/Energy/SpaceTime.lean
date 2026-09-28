import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.TimeIntegral











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] in
private lemma positive_time_germ {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    {t : ℝ} (ht : 0 < t) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x) :=
  hF.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)

omit [PreconnectedSpace M] in



theorem aestronglyMeasurable_heat_gradient_normSq (D : LeviCivitaData g)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    {s : Set ℝ} (hs : MeasurableSet s) (hspos : s ⊆ Ioi 0)
    (μ : Measure ℝ) :
    AEStronglyMeasurable (fun p : ℝ × M ↦ g.inner p.2
      (D.gradient (fun y ↦ F (p.1, y)) p.2)
      (D.gradient (fun y ↦ F (p.1, y)) p.2))
      ((μ.restrict s).prod g.volumeMeasure) := by
  let q : ℝ → M → ℝ := fun t x ↦ g.inner x
    (D.gradient (fun y ↦ F (t, y)) x) (D.gradient (fun y ↦ F (t, y)) x)
  have hqm : Measurable (fun p : Ioi (0 : ℝ) × M ↦ q p.1 p.2) := by
    apply measurable_uncurry_of_continuous_of_measurable (u := fun t : Ioi (0 : ℝ) ↦ q t)
    · intro x
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (D.hasDerivAt_gradient_normSq_of_time_derivative
        (positive_time_germ hF t.property x) (hheat t t.property)).continuousAt.comp
          continuous_subtype_val.continuousAt
    · intro t
      have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ F (t, y)) :=
        fun x ↦ (positive_time_germ hF t.property x).comp x
          (contMDiffAt_const.prodMk contMDiffAt_id)
      exact (D.continuous_inner_gradient hf hf).measurable
  let τ : ℝ → ℝ := (Ioi 0).piecewise id (fun _ ↦ 1)
  have hτ : Measurable τ := measurable_id.piecewise measurableSet_Ioi measurable_const
  have hτpos (t : ℝ) : 0 < τ t := by
    by_cases ht : 0 < t
    · simp [τ, ht]
    · simp [τ, ht]
  let σ : ℝ → Ioi (0 : ℝ) := fun t ↦ ⟨τ t, hτpos t⟩
  have hσ : Measurable σ := hτ.subtype_mk
  have hm : StronglyMeasurable (fun p : ℝ × M ↦ q (σ p.1) p.2) :=
    (hqm.comp ((hσ.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  apply hm.aestronglyMeasurable.congr
  have hp : ∀ᵐ p : ℝ × M ∂(μ.restrict s).prod g.volumeMeasure, p.1 ∈ s :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hs)
  filter_upwards [hp] with p hp
  simp only [σ, τ, piecewise, hspos hp, if_true, id_eq]
  rfl



theorem integrable_heat_energy_cutoff_from_zero (D : LeviCivitaData g)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hFc : ContinuousOn F (Ici 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) {b : ℝ} (hb : 0 < b) :
    Integrable (fun p : ℝ × M ↦ η p.2 ^ 2 * g.inner p.2
      (D.gradient (fun y ↦ F (p.1, y)) p.2)
      (D.gradient (fun y ↦ F (p.1, y)) p.2))
      ((volume.restrict (Ioc 0 b)).prod g.volumeMeasure) := by
  have hm := ((hη.continuous.comp continuous_snd).pow 2).aestronglyMeasurable.mul
    (D.aestronglyMeasurable_heat_gradient_normSq hF hheat (s := Ioc 0 b) measurableSet_Ioc
      (fun _ ht ↦ ht.1) volume)
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ F (t, y)) :=
      fun x ↦ (positive_time_germ hF ht.1 x).comp x
        (contMDiffAt_const.prodMk contMDiffAt_id)
    exact ((hη.continuous.pow 2).mul (D.continuous_inner_gradient hf hf)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hηc.isCompact (by
        intro x hx
        by_contra h
        exact hx (by simp [image_eq_zero_of_notMem_tsupport h])))
  · have hi := (D.integrated_heat_energy_cutoff_estimate_from_zero hF hFc hheat hη hηc hb).1.1
    apply hi.congr
    filter_upwards [] with t
    apply integral_congr_ae
    filter_upwards [] with x
    symm
    apply Real.norm_of_nonneg
    apply mul_nonneg (sq_nonneg _)
    by_cases hv : D.gradient (fun y ↦ F (t, y)) x = 0
    · simp [hv]
    · exact (g.pos x _ hv).le


theorem integral_heat_energy_cutoff_eq_intervalIntegral (D : LeviCivitaData g)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hFc : ContinuousOn F (Ici 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) {b : ℝ} (hb : 0 < b) :
    (∫ p : ℝ × M, η p.2 ^ 2 * g.inner p.2
      (D.gradient (fun y ↦ F (p.1, y)) p.2)
      (D.gradient (fun y ↦ F (p.1, y)) p.2)
      ∂((volume.restrict (Ioc 0 b)).prod g.volumeMeasure)) =
    ∫ t in 0..b, ∫ x, η x ^ 2 * g.inner x
      (D.gradient (fun y ↦ F (t, y)) x)
      (D.gradient (fun y ↦ F (t, y)) x) ∂g.volumeMeasure := by
  rw [integral_prod _ (D.integrable_heat_energy_cutoff_from_zero hF hFc hheat hη hηc hb),
    intervalIntegral.integral_of_le hb.le]

end PoincareConjecture.LeviCivitaData
