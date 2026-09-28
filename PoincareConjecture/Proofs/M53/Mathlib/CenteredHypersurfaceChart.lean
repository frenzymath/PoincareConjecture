import PoincareConjecture.Proofs.M53.Mathlib.EmbeddedLocalSlice
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Algebra.Group.Basic











set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace Manifold

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace E' N]
  {n : ℕ∞ω} {f : M → N}




theorem IsImmersionAtOfComplement.exists_centered_zero_slice_chart
    {x : M} (h : IsImmersionAtOfComplement ℝ 𝓘(ℝ, E) 𝓘(ℝ, E') n f x)
    (hf : IsEmbedding f) :
    ∃ e : OpenPartialHomeomorph N (E × ℝ), f x ∈ e.source ∧ e (f x) = 0 ∧
      ∀ y ∈ e.source, y ∈ range f ↔ (e y).2 = 0 := by
  obtain ⟨V, hV, hxV, _, hslice⟩ := h.exists_isOpen_range_iff hf
  let e0 := h.codChart.transHomeomorph
    (h.equiv.symm.toHomeomorph.trans (Homeomorph.subRight (h.domChart x, (0 : ℝ))))
  let e := e0.restrOpen V hV
  refine ⟨e, ⟨h.mem_codChart_source, hxV⟩, ?_, ?_⟩
  · change h.equiv.symm (h.codChart (f x)) - (h.domChart x, (0 : ℝ)) = 0
    rw [h.writtenInCharts_source h.mem_domChart_source, h.equiv.symm_apply_apply, sub_self]
  · intro y hy
    change y ∈ range f ↔ (h.equiv.symm (h.codChart y)).2 - (0 : ℝ) = 0
    simpa only [sub_zero] using hslice y hy.2





theorem IsSmoothEmbedding.exists_centered_zero_slice_chart
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E') n f)
    (hdim : Module.finrank ℝ E' = Module.finrank ℝ E + 1) (x : M) :
    ∃ e : OpenPartialHomeomorph N (E × ℝ), f x ∈ e.source ∧ e (f x) = 0 ∧
      ∀ y ∈ e.source, y ∈ range f ↔ (e y).2 = 0 := by
  obtain ⟨F, instF, instℝF, h⟩ := hf.isImmersion.isImmersionAt x
  let := instF
  let := instℝF
  let : FiniteDimensional ℝ (E × F) := h.equiv.symm.toLinearEquiv.finiteDimensional
  let : FiniteDimensional ℝ F :=
    FiniteDimensional.of_injective (LinearMap.inr ℝ E F) (by
      intro a b hab
      exact congrArg Prod.snd hab)
  have hsum := h.equiv.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod, hdim] at hsum
  let eF : F ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by
    rw [Module.finrank_self]
    omega)
  exact (h.trans_F eF).exists_centered_zero_slice_chart hf.isEmbedding

end Manifold
