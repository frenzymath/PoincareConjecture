import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

set_option autoImplicit false

open Set ChartedSpace
open scoped Manifold Topology

namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem isLocallyConstant_of_mvfderiv_eq_zero {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hdf : ∀ x v, mvfderiv I f x v = 0) : IsLocallyConstant f := by
  intro s
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  let e := extChartAt I x
  have he : IsOpen e.target := isOpen_extChartAt_target x
  have he' : ∀ y ∈ e.target, MDifferentiableAt 𝓘(ℝ, E) I e.symm y :=
    fun y hy => (mdifferentiableOn_extChartAt_symm y hy).mdifferentiableAt (he.mem_nhds hy)
  have hf' : DifferentiableOn ℝ (f ∘ e.symm) e.target := by
    intro y hy
    exact ((hf (e.symm y)).comp y (he' y hy)).differentiableAt.differentiableWithinAt
  have hdf' : e.target.EqOn (fderiv ℝ (f ∘ e.symm)) 0 := by
    intro y hy
    ext v
    rw [← mfderiv_eq_fderiv]
    change mvfderiv 𝓘(ℝ, E) (f ∘ e.symm) y v = 0
    exact (mvfderiv_comp_apply y (hf (e.symm y)) (he' y hy) v).trans (hdf _ _)
  have hu := he.isOpen_inter_preimage_of_fderiv_eq_zero hf' hdf' s
  refine ⟨e.source ∩ e ⁻¹' (e.target ∩ (f ∘ e.symm) ⁻¹' s), ?_,
    isOpen_extChartAt_preimage' x hu, ?_⟩
  · intro y hy
    simpa only [mem_preimage, Function.comp_apply, e.left_inv hy.1] using hy.2.2
  · have hx' : x ∈ e.source := mem_extChartAt_source x
    refine ⟨hx', e.map_source hx', ?_⟩
    simpa only [mem_preimage, Function.comp_apply, e.left_inv hx'] using hx

theorem eq_of_mvfderiv_eq_zero [PreconnectedSpace M] {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hdf : ∀ x v, mvfderiv I f x v = 0) (x y : M) : f x = f y :=
  (isLocallyConstant_of_mvfderiv_eq_zero hf hdf).apply_eq_of_preconnectedSpace x y

theorem exists_eq_const_of_mvfderiv_eq_zero [PreconnectedSpace M] {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hdf : ∀ x v, mvfderiv I f x v = 0) : ∃ c : ℝ, ∀ x, f x = c := by
  obtain ⟨c, hc⟩ := (isLocallyConstant_of_mvfderiv_eq_zero hf hdf).exists_eq_const
  exact ⟨c, fun x => congrFun hc x⟩

end Poincare.Manifold
