import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set Function Filter
open scoped Manifold Topology ContDiff

namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SecondCountableTopology M]

theorem exists_compact_smooth_cutoff {C U : Set M} (hC : IsCompact C)
    (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ (∀ x, f x ∈ Icc 0 1) ∧
      (∀ᶠ x in 𝓝ˢ C, f x = 1) ∧
      ∀ c ∈ Ioo (0 : ℝ) 1,
        IsCompact {x | c ≤ f x} ∧ C ⊆ interior {x | c ≤ f x} ∧
          {x | c ≤ f x} ⊆ U ∧ frontier {x | c ≤ f x} ⊆ {x | f x = c} := by
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨L, hL, hCL, hLU⟩ := exists_compact_between hC hU hCU
  obtain ⟨f, hf1, hf0, hf01⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior I (n := ⊤) hC.isClosed hCL
  have hsupp : tsupport (f : M → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra h
    exact hx (hf0 x h)
  have hfcompact : HasCompactSupport (f : M → ℝ) :=
    hL.of_isClosed_subset (isClosed_tsupport _) hsupp
  refine ⟨f, f.contMDiff, hfcompact, hsupp.trans hLU, hf01, hf1, ?_⟩
  intro c hc
  have hcsupp : {x | c ≤ f x} ⊆ tsupport (f : M → ℝ) := by
    intro x hx
    apply subset_tsupport
    exact ne_of_gt (hc.1.trans_le hx)
  refine ⟨hfcompact.of_isClosed_subset (isClosed_le continuous_const f.contMDiff.continuous) hcsupp,
    ?_, hcsupp.trans (hsupp.trans hLU), ?_⟩
  · intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [((isOpen_lt continuous_const f.contMDiff.continuous).mem_nhds
      (show c < f x by rw [hf1.self_of_nhdsSet x hx]; exact hc.2))] with y hy
    exact hy.le
  · intro x hx
    exact (frontier_le_subset_eq continuous_const f.contMDiff.continuous hx).symm

end Poincare.Manifold
