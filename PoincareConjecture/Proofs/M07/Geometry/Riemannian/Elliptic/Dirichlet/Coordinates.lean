import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Elliptic.Dirichlet.WeakEquation









set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem integral_target_eq_integral_pullback_density_of_measurable
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : M → ℝ} (hf : Measurable f) :
    (∫ y in e.target, f y ∂g.volumeMeasure) =
      ∫ x in e.source, f (e x) * g.pullbackVolumeDensity e x := by
  have hmap := g.map_restrict_volumeMeasure_symm e he hei
  have hm : AEStronglyMeasurable (fun x => f (e x))
      ((g.volumeMeasure.restrict e.target).map e.symm) := by
    rw [hmap]
    exact (hf.comp_aemeasurable
      (e.continuousOn.aemeasurable e.open_source.measurableSet)).aestronglyMeasurable
  have hi := integral_map (e.symm.continuousOn.aemeasurable e.open_target.measurableSet) hm
  have hid : (∫ y in e.target, f (e (e.symm y)) ∂g.volumeMeasure) =
      ∫ y in e.target, f y ∂g.volumeMeasure :=
    setIntegral_congr_fun e.open_target.measurableSet (fun y hy => congrArg f (e.right_inv hy))
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt
  change (∫ x, f (e x) ∂(g.volumeMeasure.restrict e.target).map e.symm) =
    (∫ y in e.target, f (e (e.symm y)) ∂g.volumeMeasure) at hi
  rw [hid, hmap] at hi
  rw [← hi]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (μ := volume) (f := fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
    (s := e.source)
    ((ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable
      e.open_source.measurableSet)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (fun x => f (e x)) e.open_source.measurableSet]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  simp [pullbackVolumeDensity, ENNReal.toReal_ofReal, Real.sqrt_nonneg,
    smul_eq_mul, mul_comm]


theorem memLp_pullback_density
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (v : Lp ℝ 2 g.volumeMeasure) :
    MemLp (fun x => v (e x)) 2
      ((volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))).restrict
        e.source) := by
  rw [← g.map_restrict_volumeMeasure_symm e he hei]
  have hm : AEStronglyMeasurable (fun x => v (e x))
      ((g.volumeMeasure.restrict e.target).map e.symm) := by
    rw [g.map_restrict_volumeMeasure_symm e he hei]
    exact ((Lp.stronglyMeasurable v).measurable.comp_aemeasurable
      (e.continuousOn.aemeasurable e.open_source.measurableSet)).aestronglyMeasurable
  apply (memLp_map_measure_iff hm
    (e.symm.continuousOn.aemeasurable e.open_target.measurableSet)).mpr
  apply MemLp.ae_eq (hf_Lp := (Lp.memLp v).restrict e.target)
  filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
  simp only [Function.comp_apply, e.right_inv hy]



theorem memLp_pullback_on_compact
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (v : Lp ℝ 2 g.volumeMeasure)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source) :
    MemLp (fun x => v (e x)) 2 (volume.restrict K) := by
  obtain hKe | hKne := K.eq_empty_or_nonempty
  · simp [hKe]
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ (x) (hx : x ∈ K) := g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds (hKs hx))) (hD.mfderiv_injective (hKs hx))
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKne
    (fun y hy => (hρ y hy).1.continuousAt.continuousWithinAt)
  let c := ENNReal.ofReal (g.pullbackVolumeDensity e x)
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (hρ x hx).2).ne'
  have hct : c ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hmeasure : c • volume.restrict K ≤
      (volume.withDensity (fun y => ENNReal.ofReal (g.pullbackVolumeDensity e y))).restrict
        e.source := by
    calc
      _ = (volume.restrict K).withDensity (fun _ => c) := withDensity_const c |>.symm
      _ ≤ (volume.restrict K).withDensity
          (fun y => ENNReal.ofReal (g.pullbackVolumeDensity e y)) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
        exact ENNReal.ofReal_le_ofReal (hmin hy)
      _ = (volume.withDensity
          (fun y => ENNReal.ofReal (g.pullbackVolumeDensity e y))).restrict K :=
        (restrict_withDensity hK.measurableSet _).symm
      _ ≤ _ := Measure.restrict_mono hKs le_rfl
  have hbound := smul_le_smul_left c⁻¹ hmeasure
  rw [smul_smul, ENNReal.inv_mul_cancel hc hct, one_smul] at hbound
  exact (g.memLp_pullback_density e he hei v).of_measure_le_smul
    (ENNReal.inv_ne_top.mpr hc) hbound

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}



theorem weakEigen_integral_laplacian_coordinates
    (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (f : EnergyTest D Ω) (hs : tsupport (f : M → ℝ) ⊆ e.target) :
    (∫ x in e.source, D.laplacian f (e x) * (toL2 D Ω u) (e x) *
      g.pullbackVolumeDensity e x) =
      -lambda * ∫ x in e.source, f (e x) * (toL2 D Ω u) (e x) *
        g.pullbackVolumeDensity e x := by
  have h := weakEigen_integral_laplacian_test u lambda heigen f
  have hl : (∫ x in e.target, D.laplacian f x * (toL2 D Ω u) x ∂g.volumeMeasure) =
      ∫ x, D.laplacian f x * (toL2 D Ω u) x ∂g.volumeMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hs (D.tsupport_laplacian_subset f ht))), zero_mul]
  have hr : (∫ x in e.target, f x * (toL2 D Ω u) x ∂g.volumeMeasure) =
      ∫ x, f x * (toL2 D Ω u) x ∂g.volumeMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), zero_mul]
  rw [← hl, ← hr,
    g.integral_target_eq_integral_pullback_density_of_measurable e he hei
      (f := fun x => D.laplacian f x * (toL2 D Ω u) x)
      ((D.continuous_laplacian f.smooth).measurable.mul (Lp.stronglyMeasurable (toL2 D Ω u)).measurable),
    g.integral_target_eq_integral_pullback_density_of_measurable e he hei
      (f := fun x => f x * (toL2 D Ω u) x)
      (f.smooth.continuous.measurable.mul (Lp.stronglyMeasurable (toL2 D Ω u)).measurable)] at h
  exact h

end PoincareConjecture.LeviCivitaData.Dirichlet
