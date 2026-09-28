import PoincareConjecture.Proofs.M76.Mathlib.CenteredTorusSquareChart
import PoincareConjecture.Proofs.M76.Mathlib.TorusCrossingBandImmersion










set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip




theorem centeredSquareQuotient_mem_crossingBand_iff {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hdhalf : d < (4 * L) / 2) {x : ℝ × ℝ}
    (hx : ‖x‖ < (4 * L) / 2) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    AddCircle.centeredSquareQuotient (4 * L) x ∈ crossingBandRegion L d ↔
      (4 * L) / 2 - d < ‖x‖ := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have hxy : |x.1| < (4 * L) / 2 ∧ |x.2| < (4 * L) / 2 := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using hx
  have hxI : x.1 ∈ Ioo (-(4 * L) / 2) ((4 * L) / 2) := by
    have h := abs_lt.mp hxy.1
    constructor <;> linarith [h.1, h.2]
  have hyI : x.2 ∈ Ioo (-(4 * L) / 2) ((4 * L) / 2) := by
    have h := abs_lt.mp hxy.2
    constructor <;> linarith [h.1, h.2]
  rw [AddCircle.centeredSquareQuotient_apply]
  simp only [crossingBandRegion, mem_union, mem_prod, mem_univ, true_and, and_true]
  change ((((4 * L / 2 + x.2 : ℝ) : AddCircle (4 * L)) ∈
      ((↑) : ℝ → AddCircle (4 * L)) '' Ioo (-d) d) ∨
    (((4 * L / 2 + x.1 : ℝ) : AddCircle (4 * L)) ∈
      ((↑) : ℝ → AddCircle (4 * L)) '' Ioo (-d) d)) ↔ _
  rw [AddCircle.coe_center_mem_shortArc_iff (4 * L) hd hdhalf hyI,
    AddCircle.coe_center_mem_shortArc_iff (4 * L) hd hdhalf hxI,
    Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, lt_max_iff]
  exact or_comm




theorem outside_centeredSquareQuotient_mem_crossingBand {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (z : AddCircle (4 * L) × AddCircle (4 * L)) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    z ∉ (AddCircle.centeredSquareQuotient (4 * L)).target → z ∈ crossingBandRegion L d := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  intro hz
  rw [AddCircle.centeredSquareQuotient_target] at hz
  have hzero : (0 : AddCircle (4 * L)) ∈
      ((↑) : ℝ → AddCircle (4 * L)) '' Ioo (-d) d :=
    ⟨0, ⟨by linarith, hd⟩, by simp⟩
  by_cases h₁ : z.1 = 0
  · exact Or.inr ⟨by rw [h₁]; exact hzero, mem_univ _⟩
  · have h₂ : z.2 = 0 := by
      by_contra hn
      exact hz ⟨h₁, hn⟩
    exact Or.inl ⟨mem_univ _, by rw [h₂]; exact hzero⟩

end PLAnnularStrip
