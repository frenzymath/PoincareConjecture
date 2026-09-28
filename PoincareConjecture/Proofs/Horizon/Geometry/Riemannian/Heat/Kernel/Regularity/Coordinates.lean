import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateRepresentative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.ExhaustionPowers

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_eLpNorm_coordinate_pullback_le
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) (hVcls : closure V ⊆ e.source) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : M → ℝ,
      MemLp f 2 (g.volumeMeasure.restrict (e '' V)) →
      MemLp (fun x => f (e x)) 2 (volume.restrict V) ∧
      (eLpNorm (fun x => f (e x)) 2 (volume.restrict V)).toReal ≤
        C * (eLpNorm f 2 (g.volumeMeasure.restrict (e '' V))).toReal := by
  obtain hVe | hVne := (closure V).eq_empty_or_nonempty
  · have hVe' : V = ∅ := Set.subset_empty_iff.mp (hVe ▸ subset_closure)
    subst V
    refine ⟨1, by norm_num, ?_⟩
    intro f hf
    simp
  have hVs : V ⊆ e.source := subset_closure.trans hVcls
  have hVt : e '' V ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hVs hx)
  have hImage := e.isOpen_image_of_subset_source hVo hVs
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ (x) (hx : x ∈ closure V) := g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds (hVcls hx)))
      (hD.mfderiv_injective (hVcls hx))
  obtain ⟨x, hx, hmin⟩ := hVcl.exists_isMinOn hVne
    (fun y hy => (hρ y hy).1.continuousAt.continuousWithinAt)
  let c : ℝ≥0∞ := ENNReal.ofReal (g.pullbackVolumeDensity e x)
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (hρ x hx).2).ne'
  have hct : c ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  let ν := (volume.withDensity
    (fun y => ENNReal.ofReal (g.pullbackVolumeDensity e y))).restrict V
  have hmeasure : c • volume.restrict V ≤ ν := by
    calc
      _ = (volume.restrict V).withDensity (fun _ => c) := withDensity_const c |>.symm
      _ ≤ (volume.restrict V).withDensity
          (fun y => ENNReal.ofReal (g.pullbackVolumeDensity e y)) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem hVo.measurableSet] with y hy
        exact ENNReal.ofReal_le_ofReal (hmin (subset_closure hy))
      _ = ν := (restrict_withDensity hVo.measurableSet _).symm
  have hdom : volume.restrict V ≤ c⁻¹ • ν := by
    have h := smul_le_smul_left c⁻¹ hmeasure
    rw [smul_smul, ENNReal.inv_mul_cancel hc hct, one_smul] at h
    exact h
  have hmap : (g.volumeMeasure.restrict (e '' V)).map e.symm = ν :=
    g.map_restrict_volumeMeasure_coordinate_subset e he hei hVo.measurableSet hVs
  have heν : AEMeasurable e ν :=
    (e.continuousOn.mono hVs).aemeasurable hVo.measurableSet
  have heμ : AEMeasurable e.symm (g.volumeMeasure.restrict (e '' V)) :=
    (e.symm.continuousOn.mono hVt).aemeasurable hImage.measurableSet
  have hmapback : ν.map e = g.volumeMeasure.restrict (e '' V) := by
    rw [← hmap, AEMeasurable.map_map_of_aemeasurable (hmap ▸ heν) heμ]
    have hid : (e ∘ e.symm) =ᵐ[g.volumeMeasure.restrict (e '' V)] id := by
      filter_upwards [ae_restrict_mem hImage.measurableSet] with y hy
      exact e.right_inv (hVt hy)
    rw [Measure.map_congr hid, Measure.map_id]
  let A : ℝ≥0∞ := c⁻¹ ^ ((2 : ℝ≥0∞)⁻¹).toReal
  have hAt : A ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (ENNReal.inv_ne_top.mpr hc)
  have hA : 0 < A := ENNReal.rpow_pos
    (pos_iff_ne_zero.mpr (ENNReal.inv_ne_zero.mpr hct)) (ENNReal.inv_ne_top.mpr hc)
  refine ⟨A.toReal, ENNReal.toReal_pos hA.ne' hAt, ?_⟩
  intro f hf
  have hfmap : MemLp f 2 (ν.map e) := hmapback ▸ hf
  have hfpull : MemLp (fun x => f (e x)) 2 ν := hfmap.comp_of_map heν
  have hnorm : eLpNorm (fun x => f (e x)) 2 ν =
      eLpNorm f 2 (g.volumeMeasure.restrict (e '' V)) := by
    rw [← hmapback]
    exact (eLpNorm_map_measure hfmap.1 heν).symm
  refine ⟨hfpull.of_measure_le_smul (ENNReal.inv_ne_top.mpr hc) hdom, ?_⟩
  have hb : eLpNorm (fun x => f (e x)) 2 (volume.restrict V) ≤
      A * eLpNorm f 2 (g.volumeMeasure.restrict (e '' V)) := by
    simpa only [one_div, hnorm, A, smul_eq_mul] using
      (eLpNorm_le_of_measure_le_smul (f := fun x => f (e x)) (p := 2) hdom)
  have hbt := ENNReal.toReal_mono (ENNReal.mul_ne_top hAt hf.2.ne) hb
  simpa only [ENNReal.toReal_mul] using hbt

theorem exists_eLpNorm_coordinate_pullback_restrict_le
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) (hVcls : closure V ⊆ e.source) :
    ∃ C : ℝ, 0 < C ∧ ∀ Ω, e '' V ⊆ Ω → ∀ f : M → ℝ,
      MemLp f 2 (g.volumeMeasure.restrict Ω) →
      MemLp (fun x => f (e x)) 2 (volume.restrict V) ∧
      (eLpNorm (fun x => f (e x)) 2 (volume.restrict V)).toReal ≤
        C * (eLpNorm f 2 (g.volumeMeasure.restrict Ω)).toReal := by
  obtain ⟨C, hC, hbound⟩ :=
    g.exists_eLpNorm_coordinate_pullback_le e he hei hVo hVcl hVcls
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ f hf
  have hmeasure := Measure.restrict_mono (μ := g.volumeMeasure) hΩ le_rfl
  obtain ⟨hmem, hnorm⟩ := hbound f (hf.mono_measure hmeasure)
  refine ⟨hmem, hnorm.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hf.2.ne (eLpNorm_mono_measure f hmeasure)) hC.le

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} [NeZero n] {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

theorem eventually_eLpNorm_coordinate_laplacian_powers_exhaustion_bound
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M}
    (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (O : M) {R : ℝ} (hR : 1 ≤ R) {a b : ℝ} (ha : 0 < a)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hVo : IsOpen V)
    (hVcl : IsCompact (closure V)) (hVcls : closure V ⊆ e.source) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ q in atTop, ∀ j t, t ∈ Icc a b →
      ∀ y, (g.edist O y).toReal ≤ R →
        MemLp (fun z => ((D.laplacian)^[j]
          (fun x => heatKernelContinuousTime D (S q) t x y)) (e z)) 2
            (volume.restrict V) ∧
        (eLpNorm (fun z => ((D.laplacian)^[j]
          (fun x => heatKernelContinuousTime D (S q) t x y)) (e z)) 2
            (volume.restrict V)).toReal ≤ ((j.factorial : ℝ) / (a / 2) ^ j) * B := by
  obtain ⟨C, hC, hcoord⟩ :=
    g.exists_eLpNorm_coordinate_pullback_le e he hei hVo hVcl hVcls
  obtain ⟨B, hB, hbound⟩ :=
    exists_eLpNorm_iterate_laplacian_heatKernelContinuous_exhaustion_bound
      D hn hc hk hRic S hΩmono hcover O hR ha
  have hcompact : IsCompact (e '' closure V) :=
    hVcl.image_of_continuousOn (e.continuousOn.mono hVcls)
  obtain ⟨q₀, hq₀⟩ := hcompact.elim_directed_cover Ω (fun q => (S q).isOpen)
    (by rw [hcover]; exact subset_univ _) hΩmono.directed_le
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  filter_upwards [eventually_ge_atTop q₀] with q hq
  intro j t ht y hy
  have hVdomain : e '' V ⊆ Ω q :=
    (image_mono subset_closure).trans (hq₀.trans (hΩmono hq))
  have hVimage := e.isOpen_image_of_subset_source hVo (subset_closure.trans hVcls)
  obtain ⟨hmem, hnorm⟩ := hbound j q t ht y hy (e '' V)
    hVimage.measurableSet hVdomain
  obtain ⟨hmem', hnorm'⟩ := hcoord _ hmem
  refine ⟨hmem', hnorm'.trans ?_⟩
  calc
    _ ≤ C * (((j.factorial : ℝ) / (a / 2) ^ j) * B) :=
      mul_le_mul_of_nonneg_left hnorm hC.le
    _ = _ := by ring

end PoincareConjecture.LeviCivitaData.Dirichlet
