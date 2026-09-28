import PoincareConjecture.Proofs.M10.CalibratedTransport
import PoincareConjecture.Proofs.M49.Mathlib.PartialChartMeasurable
import PoincareConjecture.Proofs.M49.Mathlib.SmoothPartialChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transitions











set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareConjecture.M49

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]


set_option backward.isDefEq.respectTransparency false in


theorem calibratedMetricVolume_image_eq_of_partial_isometry
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (hmetric : ∀ x ∈ e.source, ∀ a b : TangentSpace (𝓡 n) x,
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x a)
        (mfderiv (𝓡 n) (𝓡 n) e x b) = g.inner x a b)
    {A : Set M} (hA : MeasurableSet A) (hAs : A ⊆ e.source) :
    calibratedMetricVolume h (e '' A) = calibratedMetricVolume g A := by
  let μ := ((calibratedMetricVolume h).restrict e.target).map e.symm
  have hlocal : ∀ x ∈ e.source, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ B : Set M, MeasurableSet B → B ⊆ V → μ B = calibratedMetricVolume g B := by
    intro x hx
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hc : ContMDiffOn (𝓡 n) (𝓡 n) 1 c c.source := contMDiffOn_chart
    have hci : ContMDiffOn (𝓡 n) (𝓡 n) 1 c.symm c.target := contMDiffOn_chart_symm
    refine ⟨c.source ∩ e.source, c.open_source.inter e.open_source,
      ⟨mem_chart_source _ _, hx⟩, ?_⟩
    intro B hB hBV
    let C := c '' B
    have hBc : B ⊆ c.source := hBV.trans inter_subset_left
    have hBe : B ⊆ e.source := hBV.trans inter_subset_right
    have hC : MeasurableSet C := c.measurableSet_image_of_subset_source hB hBc
    have hC0 : C ⊆ c.symm.source := by
      rintro _ ⟨z, hz, rfl⟩
      exact c.map_source (hBc hz)
    let d := c.symm.trans e
    have hC1 : C ⊆ d.source := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨c.map_source (hBc hz), ?_⟩
      change c.symm (c z) ∈ e.source
      rw [c.left_inv (hBc hz)]
      exact hBe hz
    have hd : ContMDiffOn (𝓡 n) (𝓡 n) 1 d d.source := by
      intro y hy
      exact ((he.contMDiffAt (e.open_source.mem_nhds hy.2)).comp y
        (hci.contMDiffAt (c.open_target.mem_nhds hy.1))).contMDiffWithinAt
    have hdi : ContMDiffOn (𝓡 n) (𝓡 n) 1 d.symm d.target := by
      intro y hy
      exact ((hc.contMDiffAt (c.open_source.mem_nhds hy.2)).comp y
        (hei.contMDiffAt (e.open_target.mem_nhds hy.1))).contMDiffWithinAt
    have himage0 : c.symm '' C = B := c.symm_image_image_of_subset_source hBc
    have himage1 : d '' C = e '' B := by
      change (e ∘ c.symm) '' C = e '' B
      rw [image_comp, himage0]
    have hJ : ∀ y ∈ C, M10.pullbackJacobian h d y =
        M10.pullbackJacobian g c.symm y := by
      intro y hy
      have hy0 := hC0 hy
      have hy1 := (hC1 hy).2
      have hD : mfderiv (𝓡 n) (𝓡 n) d y =
          (mfderiv (𝓡 n) (𝓡 n) e (c.symm y)).comp
            (mfderiv (𝓡 n) (𝓡 n) c.symm y) :=
        mfderiv_comp y
          ((he.contMDiffAt (e.open_source.mem_nhds hy1)).mdifferentiableAt one_ne_zero)
          ((hci.contMDiffAt (c.open_target.mem_nhds hy0)).mdifferentiableAt one_ne_zero)
      have hform (a b : EuclideanSpace ℝ (Fin n)) :
          M10.pullbackMetricForm h d y a b = M10.pullbackMetricForm g c.symm y a b := by
        simpa only [M10.pullbackMetricForm, ContinuousLinearMap.bilinearComp_apply,
          hD, ContinuousLinearMap.comp_apply] using!
          hmetric (c.symm y) hy1 (mfderiv (𝓡 n) (𝓡 n) c.symm y a)
            (mfderiv (𝓡 n) (𝓡 n) c.symm y b)
      unfold M10.pullbackJacobian
      congr 2
      funext i j
      exact hform _ _
    rw [M10.map_inverse_restrict_apply e (calibratedMetricVolume h) hB hBe,
      ← himage1, ← himage0,
      M10.calibratedMetricVolume_image_eq_lintegral h d hd hdi hC hC1,
      M10.calibratedMetricVolume_image_eq_lintegral g c.symm hci hc hC hC0]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hC] with y hy
    rw [hJ y hy]
  have hforward : μ A ≤ calibratedMetricVolume g A := by
    simpa only [one_mul] using M10.measure_le_mul_of_local_comparison
      (c := 1) (U := e.source) (fun x hx => by
        obtain ⟨V, hVo, hxV, hV⟩ := hlocal x hx
        exact ⟨V, hVo, hxV, fun B hB hBV => by
          simpa only [one_mul] using (hV B hB hBV).le⟩) hA hAs
  have hreverse : calibratedMetricVolume g A ≤ μ A := by
    simpa only [one_mul] using M10.measure_le_mul_of_local_comparison
      (c := 1) (U := e.source) (fun x hx => by
        obtain ⟨V, hVo, hxV, hV⟩ := hlocal x hx
        exact ⟨V, hVo, hxV, fun B hB hBV => by
          simpa only [one_mul] using (hV B hB hBV).ge⟩) hA hAs
  rw [← M10.map_inverse_restrict_apply e (calibratedMetricVolume h) hA hAs]
  exact le_antisymm hforward hreverse



theorem calibratedMetricVolume_image_eq_of_injective_isometry
    (g : RiemannianMetric n M) (h : RiemannianMetric n N) {f : M → N}
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f) (hinj : Function.Injective f)
    (hmetric : ∀ x (a b : TangentSpace (𝓡 n) x),
      h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x a)
        (mfderiv (𝓡 n) (𝓡 n) f x b) = g.inner x a b)
    {A : Set M} (hA : MeasurableSet A) :
    calibratedMetricVolume h (f '' A) = calibratedMetricVolume g A := by
  cases isEmpty_or_nonempty M with
  | inl hM =>
      have hAe : A = ∅ := Set.eq_empty_of_isEmpty A
      simp only [hAe, image_empty, measure_empty]
  | inr hM =>
      have hfi : ContMDiffOn (𝓡 n) (𝓡 n) 1 (Function.invFun f) (range f) :=
        (g.contMDiffOn_invFun_of_injective_pullback_eq h hf hinj hmetric).of_le (by simp)
      let e := smoothOpenPartialHomeomorph f (Function.invFun f) univ isOpen_univ
        hf.contMDiffOn
        (by simpa only [image_univ] using
          g.contMDiffOn_invFun_of_injective_pullback_eq h hf hinj hmetric)
        (fun _ _ => Function.leftInverse_invFun hinj _)
        (fun x _ => g.mfderiv_bijective_of_pullback_eq h x (hmetric x))
      exact calibratedMetricVolume_image_eq_of_partial_isometry g h e
        (hf.contMDiffOn.of_le (by simp))
        (by
          change ContMDiffOn (𝓡 n) (𝓡 n) 1 (Function.invFun f) (f '' univ)
          simpa only [image_univ] using hfi)
        (fun x _ => hmetric x) hA (subset_univ A)

end PoincareConjecture.M49
