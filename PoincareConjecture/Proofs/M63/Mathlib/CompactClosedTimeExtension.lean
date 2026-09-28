import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_closedTime_compact_state_extension {C : Set ℝ} {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U)) :
    ∃ g : ℝ × E → F, ContDiffOn ℝ ∞ g (C ×ˢ univ) ∧
      ∃ O : Set E, IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧ EqOn g f (C ×ˢ O) := by
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hU hKU
  have hd : Disjoint (interior K')ᶜ K :=
    disjoint_left.mpr (fun x hx hxK => hx (hKK' hxK))
  obtain ⟨eta, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
    isOpen_interior.isClosed_compl hK.isClosed hd (n := (⊤ : ℕ∞))
  have heta : ContDiff ℝ ∞ (eta : E → ℝ) := eta.contMDiff.contDiff
  let g : ℝ × E → F := fun z => eta z.2 • f z
  have hlocal : ContDiffOn ℝ ∞ g (C ×ˢ U) :=
    (heta.comp contDiff_snd).contDiffOn.smul hf
  have hg : ContDiffOn ℝ ∞ g (C ×ˢ univ) := by
    intro z hz
    by_cases hx : z.2 ∈ U
    · apply (hlocal z ⟨hz.1, hx⟩).mono_of_mem_nhdsWithin
      have hN : (univ : Set ℝ) ×ˢ U ∈ 𝓝 z :=
        (isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hx⟩
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hN] with y hy hyU
      exact ⟨hy.1, hyU.2⟩
    · have hxK' : z.2 ∈ (interior K')ᶜ := fun h => hx (hK'U (interior_subset h))
      have hzero' : g =ᶠ[𝓝 z] fun _ => (0 : F) := by
        filter_upwards [continuousAt_snd.tendsto.eventually
          (hzero.filter_mono (nhds_le_nhdsSet hxK'))] with y hy
        change eta y.2 • f y = 0
        rw [hy, zero_smul]
      exact (contDiffAt_const.congr_of_eventuallyEq hzero').contDiffWithinAt
  obtain ⟨O, hO, hKO, hOone⟩ := mem_nhdsSet_iff_exists.mp hone
  refine ⟨g, hg, O ∩ U, hO.inter hU, fun x hx => ⟨hKO hx, hKU hx⟩,
    inter_subset_right, ?_⟩
  intro z hz
  change eta z.2 • f z = f z
  rw [hOone hz.2.1, one_smul]

end PoincareConjecture.M63
