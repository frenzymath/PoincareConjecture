import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

theorem boundaryless_inverse_smooth (e : OpenPartialHomeomorph M N) {a : N}
    (ha : a ∈ e.target) (he : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e (e.symm a))
    (e' : E ≃L[ℝ] F)
    (he' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e (e.symm a) = e'.toContinuousLinearMap) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ e.symm a := by
  let c₁ := chartAt E (e.symm a)
  let c₂ := chartAt F a
  let c := c₁.symm.trans (e.trans c₂)
  have h₂ : c₂ a ∈ c₂.target := mem_chart_target F a
  have hc : c₂ a ∈ c.target := by
    change (c₂ a ∈ c₂.target ∧ c₂.symm (c₂ a) ∈ e.target) ∧
      e.symm (c₂.symm (c₂ a)) ∈ c₁.source
    rw [c₂.left_inv (mem_chart_source F a)]
    exact ⟨⟨h₂, ha⟩, mem_chart_source E (e.symm a)⟩
  have hpoint : c.symm (c₂ a) = c₁ (e.symm a) := by
    change c₁ (e.symm (c₂.symm (c₂ a))) = _
    rw [c₂.left_inv (mem_chart_source F a)]
  have hs : ContDiffAt ℝ ∞ c (c₁ (e.symm a)) := by
    simpa [c, c₁, c₂, extChartAt_coe, extChartAt_coe_symm, e.right_inv ha,
      contDiffWithinAt_univ, Function.comp_assoc]
      using (contMDiffAt_iff.mp he).2
  have hd : HasFDerivAt c e'.toContinuousLinearMap (c₁ (e.symm a)) := by
    have h := (he.mdifferentiableAt (by simp)).hasMFDerivAt.2
    rw [he'] at h
    simpa [c, c₁, c₂, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      e.right_inv ha, Function.comp_assoc] using h
  have hinv := c.contDiffAt_symm hc (hpoint ▸ hd) (hpoint ▸ hs)
  apply contMDiffAt_iff.mpr
  refine ⟨e.continuousOn_symm.continuousAt (e.open_target.mem_nhds ha), ?_⟩
  simpa [c, c₁, c₂, extChartAt_coe, extChartAt_coe_symm, contDiffWithinAt_univ]
    using hinv

end PoincareConjecture.Proofs.M11
