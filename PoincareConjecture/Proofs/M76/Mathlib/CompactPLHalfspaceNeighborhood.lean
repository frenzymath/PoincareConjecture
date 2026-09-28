import PoincareConjecture.Proofs.M76.Mathlib.CompactPLCoreCutoffs
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLRegularLevels













set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph







theorem exists_compact_PL_halfspace_neighborhood
    {M E ι : Type*} [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {A W : Set M} (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ K : Set M, IsCompact K ∧ A ⊆ interior K ∧ K ⊆ W ∧
      ∀ x ∈ frontier K,
        ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (H : OpenPartialHomeomorph M E),
          ell.contLinear v = 1 ∧ x ∈ H.source ∧ ell (H x) = 0 ∧
          (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid E) ∧
          ∀ y ∈ H.source, y ∈ K ↔ 0 ≤ ell (H y) := by
  obtain ⟨w, C, V, hC, hCW, _, hAV, hw, _, hwone, hwzero, hwPL⟩ :=
    exists_compactly_supported_PL_core_cutoff e hcompat hcover hA hW hAW
  obtain ⟨t, ht, hK, hcharts⟩ := exists_compact_PL_regular_superlevel
    e hcompat hcover hw hwPL hC hwzero
    (a := (1 / 3 : ℝ)) (b := (2 / 3 : ℝ)) (by norm_num) (by norm_num)
  have ht0 : 0 < t := lt_trans (by norm_num) ht.1
  have ht1 : t < 1 := lt_trans ht.2 (by norm_num)
  have hcore := isCompact_core_cutoff_superlevel hw hC hCW hwzero
    (hwone.mono hAV) ht0 ht1
  let K : Set M := {x | t ≤ w x}
  have hclosed : IsClosed K := isClosed_le continuous_const hw
  refine ⟨K, hK, hcore.2.1, hcore.2.2, ?_⟩
  intro x hx
  have hxt : w x = t := by
    have htx : t ≤ w x := hclosed.closure_subset hx.1
    apply le_antisymm _ htx
    apply le_of_not_gt
    intro hstrict
    have hopen : IsOpen {y | t < w y} := isOpen_lt continuous_const hw
    have hsub : {y | t < w y} ⊆ K := fun y hy => (show t < w y from hy).le
    have hxin : x ∈ interior K := interior_mono hsub
      (hopen.interior_eq.symm ▸ (show x ∈ {y | t < w y} from hstrict))
    exact hx.2 hxin
  obtain ⟨ell, v, H, hell, hxH, hHPL, hheight⟩ := hcharts x hxt
  let ell0 := ell - ContinuousAffineMap.const ℝ E t
  refine ⟨ell0, v, H, ?_, hxH, ?_, hHPL, ?_⟩
  · simpa only [ell0, ContinuousAffineMap.sub_contLinear,
      ContinuousAffineMap.const_contLinear, sub_zero] using hell
  · change ell (H x) - t = 0
    rw [hheight x hxH, hxt, sub_self]
  · intro y hy
    change t ≤ w y ↔ 0 ≤ ell (H y) - t
    rw [hheight y hy]
    exact sub_nonneg.symm

end OpenPartialHomeomorph
