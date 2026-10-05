import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A common supported time cutoff near a parameterized point

The local gauge band in Morgan-Tian Proposition 6.30, pp. 118-119.
Joint continuity supplies a product neighborhood; a scalar smooth bump
then works throughout one parameter neighborhood.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.M14

variable {P M : Type*} [TopologicalSpace P] [TopologicalSpace M]

/-- A smooth cutoff inside a prescribed open time set keeps a jointly
continuous family in an open target for all nearby parameters,
the gauge-band step of Proposition 6.30, pp. 118-119. -/
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

end PoincareMT.M14
