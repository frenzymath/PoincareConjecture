import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace FiberBundle

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (Bundle.TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]



theorem exists_contMDiff_section_through {x : M} (v : V x) :
    ∃ W : (q : M) → V q,
      ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
        (fun q => Bundle.TotalSpace.mk' F q (W q)) ∧ W x = v := by
  obtain ⟨U, hU, hZ⟩ := exists_contMDiffOn_extend (I := I) (F := F) (k := ∞) v
  obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.mp hU
  obtain ⟨f, _, hf⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    (hO.mem_nhds hxO)
  have hW := f.contMDiff.contMDiffOn.smul_section_of_tsupport hO hf (hZ.mono hOU)
  refine ⟨fun q => f q • extend F v q, hW, ?_⟩
  change f x • extend F v x = v
  rw [f.eventuallyEq_one.eq_of_nhds, Pi.one_apply, one_smul, extend_apply_self]

end FiberBundle
