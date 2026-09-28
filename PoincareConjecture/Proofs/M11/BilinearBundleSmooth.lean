import PoincareConjecture.Proofs.M11.FiniteDimensionalSmooth
import Mathlib.Geometry.Manifold.VectorBundle.Hom





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle ContinuousLinearMap
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

theorem bilinear_trivializationAt_apply (p₀ p : B)
    (hp : p ∈ (trivializationAt F E p₀).baseSet)
    (g : E p →L[ℝ] E p →L[ℝ] ℝ) (v w : F) :
    (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
      (fun p ↦ E p →L[ℝ] E p →L[ℝ] ℝ) p₀
      (TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) p g)).2 v w =
      g ((trivializationAt F E p₀).symmL ℝ p v)
        ((trivializationAt F E p₀).symmL ℝ p w) := by
  rw [hom_trivializationAt_apply]
  simp only [inCoordinates, comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _
    (show p ∈ (trivializationAt (F →L[ℝ] ℝ) (fun p ↦ E p →L[ℝ] ℝ) p₀).baseSet from
      ⟨hp, mem_univ p⟩)]
  rw [hom_trivializationAt_apply]
  simp [inCoordinates]

theorem frameVector_contMDiffAt [ContMDiffVectorBundle ∞ F E IB] (p : B) (v : F) :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, F)) ∞
      (fun x ↦ TotalSpace.mk' F x ((trivializationAt F E p).symmL ℝ x v)) p := by
  let e := trivializationAt F E p
  apply (e.contMDiffAt_section_iff (mem_baseSet_trivializationAt F E p)).mpr
  have hconst : ContMDiffAt IB 𝓘(ℝ, F) ∞ (fun _ : B ↦ v) p := contMDiffAt_const
  apply hconst.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E p)] with x hx
  have h := e.continuousLinearMapAt_symmL hx v (R := ℝ)
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hx] at h
  exact h

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {J : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [FiniteDimensional ℝ F]

theorem contMDiffWithinAt_bilinear_of_eval {b : M → B}
    {g : ∀ x, E (b x) →L[ℝ] E (b x) →L[ℝ] ℝ} {s : Set M} {p : M}
    (hb : ContMDiffWithinAt J IB ∞ b s p)
    (hg : ∀ v w, ContMDiffWithinAt J 𝓘(ℝ) ∞
      (fun x ↦ g x ((trivializationAt F E (b p)).symmL ℝ (b x) v)
        ((trivializationAt F E (b p)).symmL ℝ (b x) w)) s p) :
    ContMDiffWithinAt J (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun p ↦ E p →L[ℝ] E p →L[ℝ] ℝ) (b x) (g x)) s p := by
  apply contMDiffWithinAt_totalSpace.mpr
  refine ⟨hb, ?_⟩
  apply contMDiffWithinAt_clm_of_apply
  intro v
  apply contMDiffWithinAt_clm_of_apply
  intro w
  apply (hg v w).congr_of_eventuallyEq
  · filter_upwards [hb.continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt F E (b p)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F E (b p)))] with x hx
    exact bilinear_trivializationAt_apply (b p) (b x) hx (g x) v w
  · exact bilinear_trivializationAt_apply (b p) (b p)
      (mem_baseSet_trivializationAt F E (b p)) (g p) v w

end PoincareConjecture.Proofs.M11
