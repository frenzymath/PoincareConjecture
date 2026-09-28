import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothOpenChart
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Separation.Hausdorff











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]



theorem exists_smoothChart_near_compact (f : E → E) {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hinj : InjOn f K)
    (hd : ∀ x ∈ K, ∃ A : E ≃L[ℝ] E, HasFDerivAt f (A : E →L[ℝ] E) x) :
    ∃ e : OpenPartialHomeomorph E E,
      (e : E → E) = f ∧ K ⊆ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let V := U ∩ (fderiv ℝ f) ⁻¹' {A : E →L[ℝ] E | IsUnit A}
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have hV : IsOpen V :=
    hdf.continuousOn.isOpen_inter_preimage hU Units.isOpen
  have hKV : K ⊆ V := by
    intro x hx
    refine ⟨hKU hx, ?_⟩
    obtain ⟨A, hA⟩ := hd x hx
    change IsUnit (fderiv ℝ f x)
    rw [hA.fderiv]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr A.bijective
  have hdV (x : E) (hx : x ∈ V) :
      ∃ A : E ≃L[ℝ] E, HasFDerivAt f (A : E →L[ℝ] E) x := by
    obtain ⟨A, hA⟩ := hx.2
    refine ⟨ContinuousLinearEquiv.ofUnit A, ?_⟩
    change HasFDerivAt f (A : E →L[ℝ] E) x
    rw [hA]
    exact ((hf.contDiffAt (hU.mem_nhds hx.1)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨W, hW, hKW, hWf⟩ := hinj.exists_isOpen_superset hK
    (fun x hx => (hf.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt) (by
      intro x hx
      obtain ⟨A, hA⟩ := hd x hx
      have hfx := hf.contDiffAt (hU.mem_nhds (hKU hx))
      let e := hfx.toOpenPartialHomeomorph f hA (by simp)
      have hxe : x ∈ e.source := hfx.mem_toOpenPartialHomeomorph_source hA (by simp)
      exact ⟨e.source, e.open_source.mem_nhds hxe, e.injOn⟩)
  have hWV : IsOpen (W ∩ V) := hW.inter hV
  have hsub : W ∩ V ⊆ U := fun _ hx => hx.2.1
  have hfWV := hf.mono hsub
  have hdWV := fun x (hx : x ∈ W ∩ V) => hdV x hx.2
  have hiWV := hWf.mono (show W ∩ V ⊆ W from inter_subset_left)
  let e := smoothOpenChart f hWV hfWV hdWV hiWV
  exact ⟨e, rfl, fun x hx => ⟨hKW hx, hKV hx⟩, hsub, hfWV,
    smoothOpenChart_symm_contDiffOn f hWV hfWV hdWV hiWV⟩

end PoincareConjecture.M25.Topology3D
