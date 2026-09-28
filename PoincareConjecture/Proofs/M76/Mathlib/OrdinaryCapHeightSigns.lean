import PoincareConjecture.Proofs.M76.Mathlib.NestedPLBallBoundary

set_option autoImplicit false

open Set

namespace Set

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem mem_both_height_closures_of_ball_sublevels
    {S : Set E} (A : E → ℝ) {c b : ℝ} (hcb : c < b)
    (hc : IsFinitePLBallPair V (S ∩ {x | A x ≤ c}) (S ∩ {x | A x = c}))
    (hb : IsFinitePLBallPair V (S ∩ {x | A x ≤ b}) (S ∩ {x | A x = b}))
    {x : E} (hx : x ∈ S ∩ {x | A x = c}) :
    x ∈ closure (S ∩ {y | A y < c}) ∧ x ∈ closure (S ∩ {y | c < A y}) := by
  have hsmall : (S ∩ {y | A y ≤ c}) \ (S ∩ {y | A y = c}) =
      S ∩ {y | A y < c} := by
    ext y
    constructor
    · rintro ⟨⟨hy, hle⟩, hn⟩
      exact ⟨hy, lt_of_le_of_ne hle (fun heq => hn ⟨hy, heq⟩)⟩
    · rintro ⟨hy, hlt⟩
      change A y < c at hlt
      exact ⟨⟨hy, hlt.le⟩, fun heq => hlt.ne heq.2⟩
  have hlo := hc.closure_sdiff
  rw [hsmall] at hlo
  refine ⟨hlo.symm ▸ hc.1 hx, ?_⟩
  have hsub : S ∩ {y | A y ≤ c} ⊆ S ∩ {y | A y ≤ b} :=
    fun _ hy => ⟨hy.1, hy.2.trans hcb.le⟩
  have hn : x ∉ S ∩ {y | A y = b} :=
    fun h => hcb.ne (hx.2.symm.trans h.2)
  have hhi := hc.mem_closure_sdiff_of_nested hb hsub hx hn
  apply closure_mono _ hhi
  rintro y ⟨hy, hn⟩
  exact ⟨hy.1, show c < A y from lt_of_not_ge (fun hle => hn ⟨hy.1, hle⟩)⟩

theorem ordinary_cap_mem_both_height_closures
    {D : Set E} (A : E → ℝ) {t : ℝ} (ht : 0 < t)
    (hlevels : ∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
      IsFinitePLBallPair V (D ∩ {x | A x ≤ t * a}) (D ∩ {x | A x = t * a}))
    {c : ℝ} (hc : c ∈ Ioo (t * (2 / 3)) t)
    {x : E} (hx : x ∈ D ∩ {x | A x = c}) :
    x ∈ closure (D ∩ {y | A y < c}) ∧ x ∈ closure (D ∩ {y | c < A y}) := by
  have ha : c / t ∈ Ioc (2 / 3) 1 :=
    ⟨(lt_div_iff₀ ht).mpr (by nlinarith [hc.1]), (div_le_one ht).mpr hc.2.le⟩
  have hheight : t * (c / t) = c := by field_simp [ht.ne']
  have hsmall := hlevels (c / t) ha
  rw [hheight] at hsmall
  have hlarge := hlevels 1 ⟨by norm_num, le_rfl⟩
  simp only [mul_one] at hlarge
  exact mem_both_height_closures_of_ball_sublevels A hc.2 hsmall hlarge hx

end Set
