import PoincareConjecture.Proofs.M01.NormalizationVolume










set_option autoImplicit false

open Bundle Manifold Metric Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

universe u

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [∀ z : E, NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) z)]


theorem m01_exists_normalizedChart
    [∀ z : E, NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) z)]
    (x : M) {C : ℝ} (hC : 1 < C) :
    ∃ e : OpenPartialHomeomorph M (TangentSpace 𝓘(ℝ, E) x),
      x ∈ e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) 1 e e.source ∧
      ContMDiffOn 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) 𝓘(ℝ, E) 1 e.symm e.target ∧
      (∀ᶠ y in 𝓝 x,
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) e y‖ < C) ∧
      (∀ᶠ a in 𝓝 (e x),
        ‖mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) 𝓘(ℝ, E) e.symm a‖ < C) := by
  let t := trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let A := t.continuousLinearEquivAt ℝ x hx
  let L := t.symmL ℝ x
  let e : OpenPartialHomeomorph M (TangentSpace 𝓘(ℝ, E) x) :=
    (chartAt E x).trans A.symm.toHomeomorph.toOpenPartialHomeomorph
  have hsource : e.source = (extChartAt 𝓘(ℝ, E) x).source := by
    simp [e]
  have htarget : e.target = A ⁻¹' (extChartAt 𝓘(ℝ, E) x).target := by
    ext a
    simp [e]
  have he : (e : M → TangentSpace 𝓘(ℝ, E) x) =
      L ∘ extChartAt 𝓘(ℝ, E) x := by
    change (A.symm : E → TangentSpace 𝓘(ℝ, E) x) ∘ extChartAt 𝓘(ℝ, E) x = _
    rw [show (A.symm : E → TangentSpace 𝓘(ℝ, E) x) = L from
      t.symm_continuousLinearEquivAt_eq hx]
  have hei : (e.symm : TangentSpace 𝓘(ℝ, E) x → M) =
      (extChartAt 𝓘(ℝ, E) x).symm ∘ A := rfl
  have hxe : x ∈ e.source := by rw [hsource]; exact mem_extChartAt_source x
  have hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) 1 e e.source := by
    rw [he, hsource]
    simpa only [extChartAt_source] using
      L.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt (x := x))
  have hh : ContMDiffOn 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) 𝓘(ℝ, E) 1 e.symm e.target := by
    rw [hei, htarget]
    exact (contMDiffOn_extChartAt_symm x).comp
      A.toContinuousLinearMap.contMDiff.contMDiffOn (fun _ ha => ha)
  have hd (y : M) (hy : y ∈ e.source) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) e y =
        L ∘L t.continuousLinearMapAt ℝ y := by
    have hy' : y ∈ (chartAt E x).source := by
      simpa only [hsource, extChartAt_source] using hy
    rw [he, mfderiv_comp y L.differentiableAt.mdifferentiableAt
      (mdifferentiableAt_extChartAt hy'), mfderiv_eq_fderiv, L.fderiv]
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy']
    rfl
  have hdi (a : TangentSpace 𝓘(ℝ, E) x) (ha : a ∈ e.target) :
      mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) 𝓘(ℝ, E) e.symm a =
        (t.symmL ℝ (e.symm a)) ∘L (A : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E) := by
    have hAa : A a ∈ (extChartAt 𝓘(ℝ, E) x).target := by
      simpa only [htarget, mem_preimage] using ha
    have hy : e.symm a ∈ (chartAt E x).source := by
      simpa only [hsource, extChartAt_source] using e.map_target ha
    have hcoord : extChartAt 𝓘(ℝ, E) x (e.symm a) = A a := by
      change extChartAt 𝓘(ℝ, E) x ((extChartAt 𝓘(ℝ, E) x).symm (A a)) = A a
      exact (extChartAt 𝓘(ℝ, E) x).right_inv hAa
    have hsymm := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, E)) hy
    rw [hcoord, ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hsymm
    rw [hei, mfderiv_comp a
      ((mdifferentiableWithinAt_extChartAt_symm hAa).mdifferentiableAt
        (by simp only [ModelWithCorners.range_eq_univ, univ_mem]))
      A.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv, A.fderiv]
    rw [← hsymm]
    rfl
  refine ⟨e, hxe, hf, hh, ?_, ?_⟩
  · filter_upwards [eventually_norm_symmL_trivializationAt_self_comp_lt E
      (TangentSpace 𝓘(ℝ, E) : M → Type _) x hC, e.open_source.mem_nhds hxe] with y hy hys
    rwa [hd y hys]
  · have hcont : ContinuousAt e.symm (e x) := e.continuousAt_symm (e.map_source hxe)
    have htend : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      simpa only [e.left_inv hxe] using hcont.tendsto
    have hnorm : ∀ᶠ y in 𝓝 x,
        ‖t.symmL ℝ y ∘L (A : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E)‖ < C := by
      simpa only [A, t.coe_continuousLinearEquivAt_eq' hx] using
        (eventually_norm_symmL_trivializationAt_comp_self_lt E
          (TangentSpace 𝓘(ℝ, E) : M → Type _) x hC)
    have hev := htend.eventually hnorm
    filter_upwards [hev, e.open_target.mem_nhds (e.map_source hxe)] with a ha hat
    rw [hdi a hat]
    exact ha

end PoincareConjecture
