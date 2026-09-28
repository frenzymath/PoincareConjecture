import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare

theorem isLocalDiffeomorphAt_of_contMDiffOn_bijective_mfderiv_modelSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → M} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f U)
    {x : M} (hx : x ∈ U)
    (hbij : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f x := by
  let c := chartAt E x
  let d := chartAt E (f x)
  let F := writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) x f
  have hfx := hf.contMDiffAt (hU.mem_nhds hx)
  have hF : ContDiffAt ℝ ∞ F (c x) := by
    simpa [F, c, writtenInExtChartAt, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp hfx).2
  have hderiv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x = fderiv ℝ F (c x) := by
    rw [mfderiv, if_pos (hfx.mdifferentiableAt (by simp))]
    simp [F, c]
  have hFbij : Function.Bijective (fderiv ℝ F (c x)) := by
    rwa [hderiv] at hbij
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hdF : HasFDerivAt F (L : E →L[ℝ] E) (c x) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  let Q := hF.toOpenPartialHomeomorph F hdF (by simp)
  have hn : ∀ᶠ y in 𝓝 (c x),
      fderiv ℝ F y ∈ range (fun A : E ≃L[ℝ] E => (A : E →L[ℝ] E)) := by
    apply (hF.continuousAt_fderiv (by simp)).preimage_mem_nhds
    exact ContinuousLinearEquiv.isOpen.mem_nhds ⟨L, rfl⟩
  obtain ⟨V, hVgood, hV, hxV⟩ := mem_nhds_iff.mp hn
  let H := (c.trans (Q.trans d.symm)).restr
    (U ∩ f ⁻¹' d.source ∩ c ⁻¹' V)
  have hFc (z : M) (hz : z ∈ c.source) : F (c z) = d (f z) := by
    change d (f (c.symm (c z))) = d (f z)
    rw [c.left_inv hz]
  have hxH : x ∈ H.source := by
    rw [OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨mem_chart_source _ _, ⟨hF.mem_toOpenPartialHomeomorph_source hdF (by simp),
      ?_⟩⟩, ?_⟩
    · change F (c x) ∈ d.target
      rw [hFc x (mem_chart_source _ _)]
      exact d.map_source (mem_chart_source _ _)
    · apply mem_interior_iff_mem_nhds.mpr
      exact inter_mem (inter_mem (hU.mem_nhds hx)
        (hfx.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds (mem_chart_source _ _))))
        ((c.continuousAt (mem_chart_source _ _)).preimage_mem_nhds (hV.mem_nhds hxV))
  have heq : EqOn f H H.source := by
    intro z hz
    change f z = d.symm (F (c z))
    rw [hFc z hz.1.1, d.left_inv (interior_subset hz.2).1.2]
  have hH : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ H H.source :=
    (hf.mono (fun _ hz => (interior_subset hz.2).1.1)).congr heq.symm
  have hHi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ H.symm H.target := by
    intro y hy
    let z := H.symm y
    have hz : z ∈ H.source := H.map_target hy
    have hzc : z ∈ c.source := hz.1.1
    have hzf : f z ∈ d.source := (interior_subset hz.2).1.2
    have hzy : f z = y := (heq hz).trans (H.right_inv hy)
    have hzQ : c z ∈ Q.source := hz.1.2.1
    have hQdy : Q.symm (d y) = c z := by
      rw [← hzy, ← hFc z hzc]
      exact Q.left_inv hzQ
    have hdz : d (f z) ∈ Q.target := by
      rw [← hFc z hzc]
      exact Q.map_source hzQ
    have hFz : ContDiffAt ℝ ∞ F (c z) := by
      have hh := (contMDiffOn_chart (I := 𝓘(ℝ, E)) (n := ∞) (x := f x)).contMDiffAt
        (d.open_source.mem_nhds hzf)
      have hg := hf.contMDiffAt (hU.mem_nhds (interior_subset hz.2).1.1)
      have hc := (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞) (x := x)).contMDiffAt
        (c.open_target.mem_nhds (c.map_source hzc))
      have hdf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (d ∘ f) (c.symm (c z)) := by
        rw [c.left_inv hzc]
        exact hh.comp z hg
      exact (hdf.comp (c z) hc).contDiffAt
    obtain ⟨A, hA⟩ := hVgood (interior_subset hz.2).2
    have hdFz : HasFDerivAt F (A : E →L[ℝ] E) (c z) := by
      change (A : E →L[ℝ] E) = fderiv ℝ F (c z) at hA
      rw [hA]
      exact (hFz.differentiableAt (by simp)).hasFDerivAt
    have hQi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Q.symm (d y) := by
      have hQdz : Q.symm (d (f z)) = c z := by rw [hzy, hQdy]
      have h := Q.contDiffAt_symm hdz
        (show HasFDerivAt (Q : E → E) (A : E →L[ℝ] E) (Q.symm (d (f z))) by
          rw [hQdz]; exact hdFz)
        (show ContDiffAt ℝ ∞ (Q : E → E) (Q.symm (d (f z))) by
          rw [hQdz]; exact hFz)
      rw [hzy] at h
      exact h.contMDiffAt
    have hdy : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ d y :=
      (contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := f x)).contMDiffAt
        (d.open_source.mem_nhds (hzy ▸ hzf))
    have hci : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm (Q.symm (d y)) := by
      rw [hQdy]
      exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x)).contMDiffAt
        (c.open_target.mem_nhds (c.map_source hzc))
    exact (hci.comp y (hQi.comp y hdy)).contMDiffWithinAt
  let P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞ := {
    toPartialEquiv := H.toPartialEquiv
    open_source := H.open_source
    open_target := H.open_target
    contMDiffOn_toFun := hH
    contMDiffOn_invFun := hHi }
  exact ⟨P, hxH, heq⟩

end Poincare
