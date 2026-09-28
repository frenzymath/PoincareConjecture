import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.CompleteFlow


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [T3Space M] in
private theorem contMDiffAt_chart_gradient
    {D : LeviCivitaData g} {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (fun y => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x) y (D.gradient f y)) x := by
  have hs := (Bundle.contMDiffAt_section x).mp (D.contMDiffAt_gradient (hf x))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds
    (mem_chart_source _ x)] with y hy
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy]
  exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x) hy (D.gradient f y)

omit [T3Space M] in
theorem hasDerivAt_chart_integralCurve
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (D.gradient f)) (p : M) (t : ℝ)
    (hp : γ t ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    HasDerivAt (fun u => extChartAt (𝓡 n) p (γ u))
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t) (D.gradient f (γ t))) t := by
  have hc := ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hp).mdifferentiableAt
    (by simp)).hasMFDerivAt
  have h := hc.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply h.congr_mfderiv
  ext
  exact (congrArg (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t))
    (one_smul ℝ (D.gradient f (γ t)))).trans (one_smul ℝ _).symm



theorem contMDiff_gradientFlow
    {D : LeviCivitaData g} {f : M → ℝ} {Φ : ℝ → M → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient f))
    (hgeo : ∀ x, g.IsGeodesicOn (fun t => Φ t x) univ) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (fun z : ℝ × M => Φ z.1 z.2) := by
  rintro ⟨t, p⟩
  let c := extChartAt (𝓡 n) p
  let z₀ : ℝ × EuclideanSpace ℝ (Fin n) := (t, c p)
  let Γ : (ℝ × EuclideanSpace ℝ (Fin n)) → ℝ → M :=
    fun z u => Φ (z.1 * u) (c.symm z.2)
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (c p) :=
    (contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 n) (n := ∞) p
      (mem_extChartAt_target p)).contMDiffAt (extChartAt_target_mem_nhds p)
  have hΓ0 : Γ z₀ 0 = p := by simp [Γ, z₀, hΦ0, c]
  have hg : ∀ᶠ z in 𝓝 z₀, g.IsGeodesicOn (Γ z) univ := by
    filter_upwards [] with z
    exact fun u _ => (hgeo (c.symm z.2)).comp_mul z.1 u (mem_univ _)
  have hpnt : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
      (fun z => Γ z 0) z₀ := by
    simpa +instances only [Γ, mul_zero, hΦ0, Function.comp_def] using
      hc.comp z₀ (contMDiffAt_iff_contDiffAt.mpr contDiffAt_snd)
  have hvel : ContDiffAt ℝ ∞
      (fun z => deriv (fun u => extChartAt (𝓡 n) (Γ z₀ 0) (Γ z u)) 0) z₀ := by
    rw [hΓ0]
    have hgrad : ContDiffAt ℝ ∞
        (fun y => mfderiv (𝓡 n) (𝓡 n) c (c.symm y) (D.gradient f (c.symm y))) (c p) := by
      apply contMDiffAt_iff_contDiffAt.mp
      have hs := contMDiffAt_chart_gradient (D := D) hf p
      have hs' : ContMDiffAt (𝓡 n) (𝓡 n) ∞
          (fun y => mfderiv (𝓡 n) (𝓡 n) c y (D.gradient f y)) (c.symm (c p)) := by
        simpa only [c, extChartAt_to_inv] using hs
      exact hs'.comp (c p) hc
    have hs : ContDiffAt ℝ ∞
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          z.1 • mfderiv (𝓡 n) (𝓡 n) c (c.symm z.2) (D.gradient f (c.symm z.2))) z₀ :=
      contDiffAt_fst.smul (hgrad.comp z₀ contDiffAt_snd)
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (extChartAt_target_mem_nhds (I := 𝓡 n) p)] with z hz
    have hsource : Φ 0 (c.symm z.2) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
      rw [hΦ0]
      simpa only [c, extChartAt_source] using c.map_target hz
    have hd := hasDerivAt_chart_integralCurve (hΦ (c.symm z.2)) p 0 hsource
    rw [hΦ0] at hd
    have hd' : HasDerivAt (fun u => c (Φ u (c.symm z.2)))
        (mfderiv (𝓡 n) (𝓡 n) c (c.symm z.2) (D.gradient f (c.symm z.2))) (z.1 * 0) := by
      simpa only [mul_zero] using hd
    have hdscaled := hd'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul z.1)
    simpa only [Γ, Function.comp_def, mul_one] using hdscaled.deriv
  have hend := contMDiffAt_geodesic_endpoint hg (convex_univ : Convex ℝ (univ : Set ℝ))
    (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) hpnt hvel
  have hread : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
      (fun z => Φ z.1 (c.symm z.2)) z₀ := by
    simpa only [Γ, mul_one] using hend
  have hchart : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) ∞ (fun z : ℝ × M => (z.1, c z.2)) (t, p) :=
    contMDiffAt_fst.prodMk_space
      ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) (mem_chart_source _ p)).comp
        (t, p) contMDiffAt_snd)
  apply (hread.comp (t, p) hchart).congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓡 n) p).mem_nhds (mem_extChartAt_source p))] with z hz
  exact congrArg (Φ z.1) (c.left_inv hz).symm

end PoincareConjecture.RiemannianMetric
