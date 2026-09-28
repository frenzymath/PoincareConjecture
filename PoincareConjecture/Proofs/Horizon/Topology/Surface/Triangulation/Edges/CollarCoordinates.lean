


import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u


noncomputable def collarParameterEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

@[simp] theorem collarParameterEquiv_apply (z : EuclideanSpace ℝ (Fin 2)) :
    collarParameterEquiv z = (z 0, z 1) := rfl

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]




theorem exists_surface_normal_collar_coordinates (p : M)
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hinj : InjOn f (Icc a b))
    (hregular : ∀ t ∈ Icc a b, deriv f t ≠ 0)
    (htarget : f '' Icc a b ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target) :
    ∃ ε > 0, ∃ C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M,
      collarParameterEquiv ⁻¹' (Icc a b ×ˢ Ioo (-ε) ε) ⊆ C.source ∧
      (∀ z, C z = (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
        (Poincare.Topology.Plane.Curves.normalStrip f (collarParameterEquiv z))) ∧
      (∀ t ∈ Icc a b,
        C (collarParameterEquiv.symm (t, 0)) =
          (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm (f t)) ∧
      C.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target := by
  obtain ⟨δ, hδ, F, hFaxis, _, hFformula, hF, hFinv, _⟩ :=
    Poincare.Topology.Plane.Curves.exists_normal_collar_coordinates hf hinj hregular
  let L := collarParameterEquiv
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) p
  let H := L.toHomeomorph.toOpenPartialHomeomorph.trans F
  let C := H.trans c.symm
  have hH : ContDiffOn ℝ ∞ H H.source :=
    hF.comp L.contDiff.contDiffOn (fun _ hz => hz.2)
  have hHinv : ContDiffOn ℝ ∞ H.symm H.target :=
    L.symm.contDiff.comp_contDiffOn (hFinv.mono (fun _ hz => hz.1))
  have hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source :=
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := p)).comp
      (hH.contMDiffOn.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target :=
    hHinv.contMDiffOn.comp
      ((contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := p)).mono (fun _ hz => hz.1))
      (fun _ hz => hz.2)
  have hformula (z : EuclideanSpace ℝ (Fin 2)) :
      C z = c.symm (Poincare.Topology.Plane.Curves.normalStrip f (L z)) := by
    change c.symm (F (L z)) = _
    rw [hFformula]
  let W := L.symm ⁻¹' C.source
  have hWopen : IsOpen W := C.open_source.preimage L.symm.continuous
  have hWaxis : Icc a b ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    change (L.symm (t, 0) ∈ Set.univ ∧ L (L.symm (t, 0)) ∈ F.source) ∧
      F (L (L.symm (t, 0))) ∈ c.target
    rw [L.apply_symm_apply]
    refine ⟨⟨mem_univ _, subset_of_mem_nhdsSet hFaxis ⟨ht, rfl⟩⟩, ?_⟩
    rw [hFformula, Poincare.Topology.Plane.Curves.normalStrip_axis]
    exact htarget ⟨t, ht, rfl⟩
  have hWnhds := hWopen.mem_nhdsSet.mpr hWaxis
  rw [isCompact_Icc.nhdsSet_prod_eq isCompact_singleton, nhdsSet_singleton] at hWnhds
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hWnhds
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  have hstrip : Icc a b ×ˢ Ioo (-ε) ε ⊆ W := by
    apply (prod_mono (subset_of_mem_nhdsSet hU) ?_).trans hUV
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hεV
  refine ⟨ε, hε, C, ?_, hformula, ?_, fun _ hz => hz.1, hC, hCinv⟩
  · intro z hz
    have h := hstrip hz
    change L.symm (L z) ∈ C.source at h
    simpa only [L.symm_apply_apply] using h
  · intro t _
    rw [hformula, L.apply_symm_apply, Poincare.Topology.Plane.Curves.normalStrip_axis]

end PoincareConjecture.Topology.Surface
