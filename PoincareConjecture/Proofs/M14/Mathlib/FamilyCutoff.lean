import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension









set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M14

variable {P M : Type*} [TopologicalSpace P] [TopologicalSpace M]




theorem exists_family_time_cutoff {f : ℝ × P → M} {c : ℝ} {p : P}
    (hf : ContinuousAt f (c, p)) {V : Set M} (hV : IsOpen V) (hfp : f (c, p) ∈ V)
    {J : Set ℝ} (hJ : IsOpen J) (hc : c ∈ J) :
    ∃ N : Set P, IsOpen N ∧ p ∈ N ∧ ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      χ c = 1 ∧ tsupport χ ⊆ J ∧ ∀ s ∈ tsupport χ, ∀ q ∈ N, f (s, q) ∈ V := by
  obtain ⟨B, N, hB, hcB, hN, hpN, hsub⟩ :=
    mem_nhds_prod_iff'.mp (hf.preimage_mem_nhds (hV.mem_nhds hfp))
  obtain ⟨χ, hsupport, _, hχ, _, hχc⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) ((hB.inter hJ).mem_nhds ⟨hcB, hc⟩)
  exact ⟨N, hN, hpN, χ, hχ, hχc, fun _ hs => (hsupport hs).2,
    fun s hs q hq => hsub ⟨(hsupport hs).1, hq⟩⟩

end PoincareConjecture.M14
