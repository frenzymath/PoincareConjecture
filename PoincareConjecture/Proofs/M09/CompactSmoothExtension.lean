import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace









set_option autoImplicit false

open scoped ContDiff Topology Manifold
open Set Filter

namespace PoincareConjecture.Proofs.M09

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_extension_near_compact (U K : Set E) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (f : E → F) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ (g : E → F) (V : Set E), ContDiff ℝ ∞ g ∧ IsOpen V ∧ K ⊆ V ∧
      V ⊆ U ∧ Set.EqOn g f V := by
  have hdisjoint : Disjoint Uᶜ K := by
    rw [Set.disjoint_left]
    intro x hx hxK
    exact hx (hKU hxK)
  obtain ⟨φ, hzero, hone, _⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E))
      hU.isClosed_compl hK.isClosed hdisjoint (n := ⊤)
  let g : E → F := fun x ↦ φ x • f x
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact φ.contMDiff.contDiff.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have hlocal : ∀ᶠ y in 𝓝 x, φ y = 0 :=
        (nhds_le_nhdsSet (show x ∈ Uᶜ from hx)) hzero
      have hgeq : g =ᶠ[𝓝 x] fun _ ↦ (0 : F) := by
        filter_upwards [hlocal] with y hy
        simp only [g, hy, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hgeq
  have hnear : U ∩ {x | φ x = 1} ∈ 𝓝ˢ K :=
    inter_mem (hU.mem_nhdsSet.mpr hKU) hone
  obtain ⟨V, hV, hKV, hVsub⟩ := mem_nhdsSet_iff_exists.mp hnear
  refine ⟨g, V, hg, hV, hKV, fun x hx ↦ (hVsub hx).1, ?_⟩
  intro x hx
  change φ x • f x = f x
  rw [(hVsub hx).2, one_smul]

end PoincareConjecture.Proofs.M09
