import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Elliptic.Dirichlet.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology Bundle

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem fderiv_comp_eq_inner_gradient
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (f : EnergyTest D Ω) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => f (e y)) x v =
      g.inner (e x) (D.gradient f (e x)) (mfderiv (𝓡 n) (𝓡 n) e x v) := by
  rw [D.inner_gradient]
  have h := mvfderiv_comp x ((f.smooth (e x)).mdifferentiableAt (by simp))
    ((he.contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp))
  have h' := congrArg (fun L => L v) h
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
    ContinuousLinearMap.comp_apply] at h'
  convert! h' using 1

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem sq_fderiv_comp_le_gradient_energy
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (f : EnergyTest D Ω) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ (fun y => f (e y)) x v) ^ 2 ≤
      g.inner (e x) (D.gradient f (e x)) (D.gradient f (e x)) *
        (g.pullbackCoefficients e x v v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [fderiv_comp_eq_inner_gradient e he f hx v, pow_two]
  exact real_inner_mul_inner_self_le (D.gradient f (e x)) (mfderiv (𝓡 n) (𝓡 n) e x v)

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem exists_coordinate_derivative_bound
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : EnergyTest D Ω), ∀ x ∈ K,
      (fderiv ℝ (fun y => f (e y)) x v) ^ 2 ≤
        C * (g.inner (e x) (D.gradient f (e x)) (D.gradient f (e x)) *
          g.pullbackVolumeDensity e x) := by
  obtain hKe | hKne := K.eq_empty_or_nonempty
  · exact ⟨1, zero_lt_one, by simp [hKe]⟩
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ (x) (hx : x ∈ K) := g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds (hKs hx))) (hD.mfderiv_injective (hKs hx))
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne
    (fun y hy => (hρ y hy).1.continuousAt.continuousWithinAt)
  have hcoeff : ContinuousOn (fun y => g.pullbackCoefficients e y v v) K :=
    fun y hy => ((g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (e.open_source.mem_nhds (hKs hy)))).clm_apply
        contDiffAt_const |>.clm_apply contDiffAt_const).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcoeff
  let c := g.pullbackVolumeDensity e a
  have hc : 0 < c := (hρ a ha).2
  let b := max B 1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨b / c, div_pos hb hc, ?_⟩
  intro f x hx
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hE : 0 ≤ g.inner (e x) (D.gradient f (e x)) (D.gradient f (e x)) := by
    exact real_inner_self_nonneg (x := D.gradient f (e x))
  have hcoef : g.pullbackCoefficients e x v v ≤ b := by
    calc
      _ ≤ ‖g.pullbackCoefficients e x v v‖ := le_abs_self _
      _ ≤ b := (hB x hx).trans (le_max_left _ _)
  have hbc : b ≤ (b / c) * g.pullbackVolumeDensity e x := by
    calc
      b = (b / c) * c := (div_mul_cancel₀ b hc.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmin hx) (div_pos hb hc).le
  calc
    _ ≤ _ := sq_fderiv_comp_le_gradient_energy e he f (hKs hx) v
    _ ≤ g.inner (e x) (D.gradient f (e x)) (D.gradient f (e x)) * b :=
      mul_le_mul_of_nonneg_left hcoef hE
    _ ≤ g.inner (e x) (D.gradient f (e x)) (D.gradient f (e x)) *
        ((b / c) * g.pullbackVolumeDensity e x) :=
      mul_le_mul_of_nonneg_left hbc hE
    _ = _ := by ring

theorem integral_compact_image_eq_pullback_density
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {F : M → ℝ} (hF : Measurable F) :
    (∫ y in e '' K, F y ∂g.volumeMeasure) =
      ∫ x in K, F (e x) * g.pullbackVolumeDensity e x := by
  have hKe := hK.image_of_continuousOn (e.continuousOn.mono hKs)
  have hKt : e '' K ⊆ e.target := by rintro y ⟨x, hx, rfl⟩; exact e.map_source (hKs hx)
  have h := g.integral_target_eq_integral_pullback_density_of_measurable e he hei
    (hF.indicator hKe.measurableSet)
  rw [setIntegral_indicator hKe.measurableSet, inter_eq_right.mpr hKt] at h
  rw [h]
  calc
    _ = ∫ x in e.source, K.indicator (fun y => F (e y) * g.pullbackVolumeDensity e y) x := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro x hx
      dsimp only
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK, indicator_of_mem (mem_image_of_mem e hxK)]
      · have hxnot : e x ∉ e '' K := by
          rintro ⟨y, hy, heq⟩
          have hxy := e.injOn (hKs hy) hx heq
          exact hxK (hxy ▸ hy)
        rw [indicator_of_notMem hxK, indicator_of_notMem hxnot, zero_mul]
    _ = _ := by rw [setIntegral_indicator hK.measurableSet, inter_eq_right.mpr hKs]

theorem exists_integral_sq_coordinate_derivative_le_energy
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EnergyTest D Ω,
      (∫ x in K, (fderiv ℝ (fun y => f (e y)) x v) ^ 2) ≤ C * ‖f‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_coordinate_derivative_bound (D := D) (Ω := Ω)
    e he hei hK hKs v
  refine ⟨C, hC, ?_⟩
  intro f
  let E : M → ℝ := fun y => g.inner y (D.gradient f y) (D.gradient f y)
  have hE : Continuous E := D.continuous_inner_gradient f.smooth f.smooth
  have hEi : Integrable E g.volumeMeasure := f.integrable_gradient f
  have hEn : ∀ y, 0 ≤ E y := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    intro y
    exact real_inner_self_nonneg (x := D.gradient f y)
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) K := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hKs hx)))
      (hD.mfderiv_injective (hKs hx))).1.continuousAt.continuousWithinAt
  have hF : ContDiffOn ℝ ∞ (fun y => f (e y)) e.source :=
    (f.smooth.comp_contMDiffOn he).contDiffOn
  have hd : ContinuousOn (fun x => (fderiv ℝ (fun y => f (e y)) x v) ^ 2) K :=
    ((hF.continuousOn_fderiv_of_isOpen e.open_source (by simp)).clm_apply
      continuousOn_const).pow 2 |>.mono hKs
  have hEc : ContinuousOn (fun x => E (e x) * g.pullbackVolumeDensity e x) K :=
    (hE.comp_continuousOn (e.continuousOn.mono hKs)).mul hρ
  calc
    _ ≤ ∫ x in K, C * (E (e x) * g.pullbackVolumeDensity e x) :=
      setIntegral_mono_on (hd.integrableOn_compact hK)
        ((continuousOn_const.mul hEc).integrableOn_compact hK) hK.measurableSet
        (fun x hx => hbound f x hx)
    _ = C * ∫ y in e '' K, E y ∂g.volumeMeasure := by
      rw [integral_const_mul, integral_compact_image_eq_pullback_density e he hei hK hKs hE.measurable]
    _ ≤ C * ∫ y, E y ∂g.volumeMeasure :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hEi (Eventually.of_forall hEn)) hC.le
    _ ≤ C * ‖f‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [f.norm_sq]
      exact le_add_of_nonneg_left (integral_nonneg fun y => mul_self_nonneg (f y))

end PoincareConjecture.LeviCivitaData.Dirichlet
