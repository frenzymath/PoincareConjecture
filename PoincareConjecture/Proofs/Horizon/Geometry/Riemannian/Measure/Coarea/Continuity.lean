import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Global








set_option autoImplicit false

open Set Function MeasureTheory TopologicalSpace
open Poincare.EuclideanSpace Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.RiemannianMetric

private theorem continuous_integral_euclideanCons {n : ℕ}
    {F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) :
    Continuous (fun c : ℝ => ∫ y : EuclideanSpace ℝ (Fin n), F (euclideanCons c y)) := by
  let K := euclideanTail '' tsupport F
  have hK : IsCompact K := hFc.isCompact.image (continuous_euclideanTail n)
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support hK
  · have h := hF.comp (euclideanConsCLE n).continuous
    exact h.continuousOn
  · intro c y _ hy
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hy ⟨euclideanCons c y, hmem, euclideanTail_cons c y⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M)
  (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)

include hf in

theorem hasCompactSupport_regularLevelIntegral
    {h : M → ℝ} (hc : HasCompactSupport h) :
    HasCompactSupport (fun c : ℝ => ∫ z, h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c) := by
  apply HasCompactSupport.intro (hc.isCompact.image hf.continuous)
  intro c hc
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  apply image_eq_zero_of_notMem_tsupport
  intro hz
  exact hc ⟨openLevelIncl f U c z, hz, z.2⟩

include hf hreg in

theorem continuous_regularLevelIntegral_of_chart_support
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1))) M)
    (heU : e.target ⊆ U) (hef : ∀ y ∈ e.source, f (e y) = y 0)
    (he : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e.symm e.target)
    {h : M → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ e.target) :
    Continuous (fun c : ℝ => ∫ z, h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c) := by
  let F := fun x => chartPullback e h x * g.levelCoordinateDensity e x
  have hD : e.MDifferentiable (𝓡 (n + 1)) (𝓡 (n + 1)) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt
  have hσ : ContinuousOn (g.levelCoordinateDensity e) e.source := by
    apply (hρ.mul ((g.continuous_tangentNorm_gradient hf).comp_continuousOn e.continuousOn)).congr
    intro x hx
    exact g.levelCoordinateDensity_eq_mul_gradient_norm hf e hef he hei hx
  have hF : Continuous F :=
    ((continuous_chartPullback e hh hc hs).continuousOn.mul hσ).continuous_of_tsupport_subset
      e.open_source (tsupport_mul_subset_left.trans (tsupport_chartPullback_subset_source e hc hs))
  have hFc : HasCompactSupport F := (hasCompactSupport_chartPullback e hc hs).mul_right
  apply (continuous_integral_euclideanCons hF hFc).congr
  intro c
  rw [g.integral_regularLevel_of_support_subset hf U hreg c e heU hef he hei
    hh.continuousOn ((subset_tsupport h).trans hs)]
  rw [← integral_indicator (e.open_source.preimage (contDiff_euclideanCons c).continuous).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : euclideanCons c y ∈ e.source
  · simp [F, chartPullback, hy]
  · simp [F, chartPullback, hy]

include hf hreg in


theorem continuous_regularLevelIntegral
    {h : M → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ U) :
    Continuous (fun c : ℝ => ∫ z, h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c) := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (n + 1))) M
  let eAt : ∀ p : M, p ∈ tsupport h →
      OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1))) M := fun p hp =>
    Classical.choose (exists_regular_coordinates hf U (hs hp) (hreg p (hs hp)))
  have eAt_target : ∀ (p : M) (hp : p ∈ tsupport h), p ∈ (eAt p hp).target :=
    fun p hp => (Classical.choose_spec (exists_regular_coordinates hf U (hs hp)
      (hreg p (hs hp)))).1
  have eAt_subset : ∀ (p : M) (hp : p ∈ tsupport h), (eAt p hp).target ⊆ U :=
    fun p hp => (Classical.choose_spec (exists_regular_coordinates hf U (hs hp)
      (hreg p (hs hp)))).2.1
  have eAt_smooth : ∀ (p : M) (hp : p ∈ tsupport h),
      ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (eAt p hp) (eAt p hp).source :=
    fun p hp => (Classical.choose_spec (exists_regular_coordinates hf U (hs hp)
      (hreg p (hs hp)))).2.2.1
  have eAt_smooth_symm : ∀ (p : M) (hp : p ∈ tsupport h),
      ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (eAt p hp).symm (eAt p hp).target :=
    fun p hp => (Classical.choose_spec (exists_regular_coordinates hf U (hs hp)
      (hreg p (hs hp)))).2.2.2.1
  have eAt_level : ∀ (p : M) (hp : p ∈ tsupport h) (y : EuclideanSpace ℝ (Fin (n + 1))),
      y ∈ (eAt p hp).source → f ((eAt p hp) y) = y 0 :=
    fun p hp => (Classical.choose_spec (exists_regular_coordinates hf U (hs hp)
      (hreg p (hs hp)))).2.2.2.2
  have hcover : tsupport h ⊆ ⋃ p : tsupport h, (eAt p p.2).target := by
    intro x hx
    exact mem_iUnion_of_mem ⟨x, hx⟩ (eAt_target x hx)
  obtain ⟨s, H, hHcont, hHcompact, hHsupport, hHsum⟩ :=
    Poincare.Coarea.exists_finite_continuous_decomposition
      (fun p : tsupport h => (eAt p p.2).target)
      (fun p => (eAt p p.2).open_target) hh hc hcover
  have hlocal : ∀ i : s, Continuous (fun c : ℝ => ∫ z, H i (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c) := fun i =>
    g.continuous_regularLevelIntegral_of_chart_support hf U hreg (eAt i.1 i.1.2)
      (eAt_subset i.1 i.1.2) (eAt_level i.1 i.1.2) (eAt_smooth i.1 i.1.2)
      (eAt_smooth_symm i.1 i.1.2) (hHcont i) (hHcompact i)
      ((hHsupport i).trans inter_subset_left)
  have hinner : ∀ (c : ℝ) (i : s), Integrable (fun z => H i (openLevelIncl f U c z))
      (g.regularLevelVolume hf U hreg c) := fun c i =>
    g.integrable_regularLevelVolume_of_hasCompactSupport hf U hreg c
      (hHcont i) (hHcompact i) (((hHsupport i).trans inter_subset_right).trans hs)
  apply (continuous_finsetSum Finset.univ (fun i _ => hlocal i)).congr
  intro c
  rw [← integral_finsetSum _ (fun i _ => hinner c i)]
  apply integral_congr_ae
  filter_upwards [] with z
  exact hHsum (openLevelIncl f U c z)

end PoincareConjecture.RiemannianMetric
