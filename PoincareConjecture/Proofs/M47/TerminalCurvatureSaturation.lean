import Mathlib.Topology.MetricSpace.Thickening









set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M47

variable {M : Type*} [MetricSpace M] [ConnectedSpace M]



theorem terminalCurvature_compact_saturation_eq_univ
    (Phi : ℝ → M → M) (hzero : ∀ x, Phi 0 x = x)
    (hadd : ∀ s t x, Phi (s + t) x = Phi s (Phi t x))
    (hiso : ∀ t, Isometry (Phi t)) {K : Set M} (hK : IsCompact K)
    (hne : K.Nonempty)
    (hopen : IsOpen {x | ∃ t : ℝ, ∃ k ∈ K, Phi t k = x}) :
    {x | ∃ t : ℝ, ∃ k ∈ K, Phi t k = x} = univ := by
  let S : Set M := {x | ∃ t : ℝ, ∃ k ∈ K, Phi t k = x}
  have hKS : K ⊆ S := fun x hx => ⟨0, x, hx, hzero x⟩
  obtain ⟨epsilon, hepsilon, hbuffer⟩ := hK.exists_thickening_subset_open hopen hKS
  have hSS : thickening epsilon S ⊆ S := by
    intro y hy
    obtain ⟨z, hz, hdist⟩ := mem_thickening_iff.mp hy
    obtain ⟨t, k, hk, hzk⟩ := hz
    have hnear : Phi (-t) y ∈ thickening epsilon K := by
      apply mem_thickening_iff.mpr
      refine ⟨k, hk, ?_⟩
      have hd := (hiso (-t)).dist_eq y z
      rw [← hzk, ← hadd, neg_add_cancel, hzero] at hd
      rw [hzk] at hd
      exact hd.trans_lt hdist
    obtain ⟨s, q, hq, he⟩ := hbuffer hnear
    refine ⟨t + s, q, hq, ?_⟩
    rw [hadd, he, ← hadd, add_neg_cancel, hzero]
  exact (IsClopen.of_thickening_subset_self hepsilon hSS).eq_univ (hne.mono hKS)



theorem terminalCurvature_invariant_bounded_of_compact_saturation
    (Phi : ℝ → M → M) (hzero : ∀ x, Phi 0 x = x)
    (hadd : ∀ s t x, Phi (s + t) x = Phi s (Phi t x))
    (hiso : ∀ t, Isometry (Phi t)) {K : Set M} (hK : IsCompact K)
    (hne : K.Nonempty)
    (hopen : IsOpen {x | ∃ t : ℝ, ∃ k ∈ K, Phi t k = x})
    (f : M → ℝ) (hf : ContinuousOn f K) (hinvariant : ∀ t x, f (Phi t x) = f x) :
    ∃ B : ℝ, ∀ x, f x ≤ B := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image hf
  have hfull := terminalCurvature_compact_saturation_eq_univ Phi hzero hadd hiso hK hne hopen
  refine ⟨B, fun x => ?_⟩
  obtain ⟨t, k, hk, hpoint⟩ := (hfull.symm ▸ mem_univ x)
  rw [← hpoint, hinvariant]
  exact hB (mem_image_of_mem f hk)

end PoincareConjecture.M47
