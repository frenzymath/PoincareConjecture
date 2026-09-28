import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold

theorem mfderiv_pi_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    {ι : Type*} [Fintype ι]
    (f : ι → M → ℝ) (hf : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f i))
    (x : M) (v : TangentSpace 𝓘(ℝ, E) x) (i : ι) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ι → ℝ) (fun y i => f i y) x v i =
      mvfderiv 𝓘(ℝ, E) (f i) x v := by
  let c := extChartAt 𝓘(ℝ, E) x
  have hjoint : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ι → ℝ) ∞ (fun y i => f i y) :=
    contMDiff_pi_space.mpr hf
  have hi (j : ι) : HasFDerivAt (f j ∘ c.symm)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f j) x) (c x) := by
    simpa [c, writtenInExtChartAt, hasFDerivWithinAt_univ] using
      ((hf j x).mdifferentiableAt (by simp)).hasMFDerivAt.2
  have hJ : HasFDerivAt (fun z j => f j (c.symm z))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ι → ℝ) (fun y i => f i y) x) (c x) := by
    simpa [c, writtenInExtChartAt, hasFDerivWithinAt_univ] using
      ((hjoint x).mdifferentiableAt (by simp)).hasMFDerivAt.2
  exact congrArg (fun L => L v i) (hJ.unique (hasFDerivAt_pi.mpr hi))

private theorem exists_smooth_local_equiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {x : E} (hx : x ∈ s)
    (hd : HasFDerivAt f (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) x) :
    ∃ G : OpenPartialHomeomorph E E, G.source ⊆ s ∧ x ∈ G.source ∧
      (G : E → E) = f ∧ ContDiffOn ℝ ∞ G G.source ∧
      ContDiffOn ℝ ∞ G.symm G.target := by
  have hfx := hf.contDiffAt (hs.mem_nhds hx)
  let G₀ := hfx.toOpenPartialHomeomorph f hd (by simp)
  have hxG : x ∈ G₀.source := hfx.mem_toOpenPartialHomeomorph_source hd (by simp)
  let t : Set E := (s ∩ G₀.source) ∩ (fderiv ℝ f) ⁻¹' {L : E →L[ℝ] E | IsUnit L}
  have ht : IsOpen t := by
    apply ContinuousOn.isOpen_inter_preimage
    · exact (hf.continuousOn_fderiv_of_isOpen hs (by exact_mod_cast le_top)).mono
        inter_subset_left
    · exact hs.inter G₀.open_source
    · exact Units.isOpen
  have hxt : x ∈ t := by
    refine ⟨⟨hx, hxG⟩, ?_⟩
    change IsUnit (fderiv ℝ f x)
    rw [hd.fderiv, show (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) = 1 from
      ContinuousLinearMap.ext fun y => by simp [ContinuousLinearMap.one_def]]
    exact isUnit_one
  let G := G₀.restrOpen t ht
  refine ⟨G, fun y hy => hy.2.1.1, ⟨hxG, hxt⟩, rfl, ?_, ?_⟩
  · exact hf.mono fun y hy => hy.2.1.1
  · intro y hy
    have hys := G.map_target hy
    have hyf : G.symm y ∈ s := hys.2.1.1
    have hyu : IsUnit (fderiv ℝ f (G.symm y)) := hys.2.2
    have hd' : HasFDerivAt f
        (ContinuousLinearEquiv.ofUnit hyu.unit : E →L[ℝ] E) (G.symm y) := by
      convert ((hf.contDiffAt (hs.mem_nhds hyf)).differentiableAt (by simp)).hasFDerivAt
        using 1
      exact ContinuousLinearMap.ext fun z => by
        simp [ContinuousLinearEquiv.ofUnit, IsUnit.unit_spec]
    exact (G.contDiffAt_symm hy hd' (hf.contDiffAt (hs.mem_nhds hyf))).contDiffWithinAt

theorem exists_projection_chart_of_surjective_mfderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → F} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (x : M)
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    ∃ e : E ≃L[ℝ] (F × (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x : E →L[ℝ] F).ker),
      ∃ d : OpenPartialHomeomorph M E, x ∈ d.source ∧
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ d d.source ∧
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ d.symm d.target ∧
        ∀ y ∈ d.target, f (d.symm y) = (e y).1 := by
  let c := chartAt E x
  let u := c x
  let fc : E → F := f ∘ c.symm
  let L : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  have hfc : ContDiffOn ℝ ∞ fc c.target := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact hf.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x))
  have hd : HasFDerivAt fc L u := by
    have h := ((hf x).mdifferentiableAt (by simp)).hasMFDerivAt.2
    simpa [fc, L, u, c, writtenInExtChartAt, hasFDerivWithinAt_univ] using h
  obtain ⟨p, hp⟩ := L.ker_closedComplemented_of_finiteDimensional_range
  let e : E ≃L[ℝ] (F × L.ker) := L.equivProdOfSurjectiveOfIsCompl p
    (LinearMap.range_eq_top.mpr hsurj) (LinearMap.range_eq_of_proj hp)
    (LinearMap.isCompl_of_proj hp)
  let H : E → E := fun v => e.symm (fc v, p v)
  have hH : ContDiffOn ℝ ∞ H c.target :=
    e.symm.contDiff.comp_contDiffOn (hfc.prodMk p.contDiff.contDiffOn)
  have hHd : HasFDerivAt H (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) u := by
    convert e.symm.hasFDerivAt.comp u (hd.prodMk p.hasFDerivAt) using 1
    · rfl
    · ext v
      exact (e.symm_apply_apply v).symm
  obtain ⟨G, hGc, huG, hG, hGs, hGis⟩ :=
    exists_smooth_local_equiv c.open_target hH (mem_chart_target E x) hHd
  let d := c.trans G
  have hdsource : x ∈ d.source := ⟨mem_chart_source E x, huG⟩
  have hds : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ d d.source := by
    exact hGs.contMDiffOn.comp
      ((contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := x)).mono inter_subset_left)
      (fun y hy => hy.2)
  have hdis : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ d.symm d.target := by
    exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x)).comp
      (hGis.contMDiffOn.mono inter_subset_left) (fun y hy => hy.2)
  refine ⟨e, d, hdsource, hds, hdis, ?_⟩
  intro y hy
  have hyG : y ∈ G.target := hy.1
  have hyinv : H (G.symm y) = y := by rw [← hG]; exact G.right_inv hyG
  have heq := congrArg (fun z => (e z).1) hyinv
  change f (d.symm y) = (e y).1
  simpa [d, H, fc, Function.comp_def] using heq

theorem isSubmersionAt_of_surjective_mfderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → F} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (x : M)
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    Manifold.IsSubmersionAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
  obtain ⟨e, d, hx, hd, hdi, heq⟩ :=
    exists_projection_chart_of_surjective_mfderiv hf x hsurj
  let L : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  change E ≃L[ℝ] (F × L.ker) at e
  apply Manifold.IsSubmersionAt.mk_of_charts e d (OpenPartialHomeomorph.refl F)
    hx (by simp) (d.mem_maximalAtlas_of_contMDiffOn hd hdi)
    (OpenPartialHomeomorph.refl F |>.mem_maximalAtlas_of_contMDiffOn
      contMDiffOn_id contMDiffOn_id) (by simp)
  intro y hy
  change f (d.symm y) = (e y).1
  exact heq y hy.2

end Poincare.Geometry.Manifold
