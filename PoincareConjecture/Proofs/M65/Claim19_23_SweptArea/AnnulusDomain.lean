import PoincareConjecture.Definitions.M64Annulus

set_option autoImplicit false

open Set

namespace PoincareConjecture

theorem m65AnnulusDomain_isCompact : IsCompact m64AnnulusDomain := by
  have hmap : Continuous (fun p : ℝ × ℝ => annulusPoint p.1 p.2) := by
    unfold annulusPoint
    fun_prop
  have heq : m64AnnulusDomain =
      (fun p : ℝ × ℝ => annulusPoint p.1 p.2) '' (Icc 0 curvePeriod ×ˢ Icc (0 : ℝ) 1) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z 0, z 1), ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩, ?_⟩
      ext i
      fin_cases i <;> rfl
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image hmap

theorem m65AnnulusDomain_convex : Convex ℝ m64AnnulusDomain := by
  intro x hx y hy u v hu hv huv
  have h0 := (convex_Icc (0 : ℝ) curvePeriod) ⟨hx.1, hx.2.1⟩ ⟨hy.1, hy.2.1⟩ hu hv huv
  have h1 := (convex_Icc (0 : ℝ) 1) hx.2.2 hy.2.2 hu hv huv
  exact ⟨h0.1, h0.2, h1.1, h1.2⟩

end PoincareConjecture
