import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false

open Set
open scoped InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem range_eq_normal_perp (A : V →L[ℝ] E) (hA : Function.Injective A)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ V + 1)
    (n : E) (hn : n ≠ 0) (hnA : ∀ v, ⟪n, A v⟫_ℝ = 0) :
    A.range = (ℝ ∙ n)ᗮ := by
  let : Fact (Module.finrank ℝ E = Module.finrank ℝ V + 1) := ⟨hdim⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro x ⟨v, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hnA v)
  · rw [LinearMap.finrank_range_of_inj hA,
      Submodule.finrank_orthogonal_span_singleton (n := Module.finrank ℝ V) hn]

theorem height_annihilates_iff_normal_sign (A : V →L[ℝ] E) (hA : Function.Injective A)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ V + 1)
    (n u : E) (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) (hnA : ∀ v, ⟪n, A v⟫_ℝ = 0) :
    (∀ v, ⟪u, A v⟫_ℝ = 0) ↔ u = n ∨ u = -n := by
  have hn0 : n ≠ 0 := by intro h; simp only [h, norm_zero] at hn; norm_num at hn
  have hrange := range_eq_normal_perp A hA hdim n hn0 hnA
  constructor
  · intro h
    have horth : u ∈ A.rangeᗮ := (A.range.mem_orthogonal' u).mpr (by
      rintro x ⟨v, rfl⟩
      exact h v)
    rw [hrange, Submodule.orthogonal_orthogonal] at horth
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp horth
    have habs : |a| = 1 := by
      have hnorm := congrArg norm ha
      simpa only [norm_smul, Real.norm_eq_abs, hn, hu, mul_one] using hnorm
    have haa : a * a = 1 := by nlinarith [sq_abs a]
    rcases mul_self_eq_one_iff.mp haa with hpos | hneg
    · left
      simpa only [hpos, one_smul] using ha.symm
    · right
      simpa only [hneg, neg_one_smul] using ha.symm
  · rintro (rfl | rfl)
    · exact hnA
    · intro v
      rw [inner_neg_left, hnA v, neg_zero]

end PoincareConjecture.M25.Topology3D
