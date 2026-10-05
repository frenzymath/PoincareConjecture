import Mathlib.Topology.Instances.AddCircle.Real

/-!
# The exact endpoint identifications in a closed period interval

The quotient of [0,p] identifies only its two endpoints. These
equalities retain the full paired faces in the solid-torus cut.
See Waldhausen 1968, pp. 59--60, and rigidity derivation 002.
-/

set_option autoImplicit false

open Set

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

/-- On the whole closed period interval, precisely its two
endpoints represent the original circle origin. See derivation 002. -/
theorem coe_eq_zero_iff_endpoints {t : ℝ} (ht : t ∈ Icc 0 p) :
    (t : AddCircle p) = 0 ↔ t = 0 ∨ t = p := by
  by_cases htp : t = p
  · subst t
    simp only [coe_period, or_true]
  · rw [coe_eq_zero_iff_of_mem_Ico ⟨ht.1, lt_of_le_of_ne ht.2 htp⟩]
    simp only [htp, or_false]

/-- Two points of the complete closed period interval have the
same circle image exactly when they coincide or are the paired
endpoints. No other cut points are identified. See derivation 002. -/
theorem coe_eq_coe_iff_eq_or_endpoints {t u : ℝ}
    (ht : t ∈ Icc 0 p) (hu : u ∈ Icc 0 p) :
    (t : AddCircle p) = (u : AddCircle p) ↔
      t = u ∨ (t = 0 ∧ u = p) ∨ (t = p ∧ u = 0) := by
  constructor
  · intro h
    by_cases htp : t = p
    · subst t
      have hu0 : u = 0 ∨ u = p :=
        (coe_eq_zero_iff_endpoints hu).mp (h.symm.trans (coe_period p))
      rcases hu0 with hu0 | hup
      · exact Or.inr (Or.inr ⟨rfl, hu0⟩)
      · exact Or.inl hup.symm
    · by_cases hup : u = p
      · subst u
        have ht0 : t = 0 ∨ t = p :=
          (coe_eq_zero_iff_endpoints ht).mp (h.trans (coe_period p))
        exact Or.inr (Or.inl ⟨ht0.resolve_right htp, rfl⟩)
      · left
        apply (coe_eq_coe_iff_of_mem_Ico
          (a := 0) (p := p) ?_ ?_).mp h
        · simpa only [zero_add] using
            (show t ∈ Ico 0 p from ⟨ht.1, lt_of_le_of_ne ht.2 htp⟩)
        · simpa only [zero_add] using
            (show u ∈ Ico 0 p from ⟨hu.1, lt_of_le_of_ne hu.2 hup⟩)
  · rintro (htu | ⟨ht0, hup⟩ | ⟨htp, hu0⟩)
    · rw [htu]
    · rw [ht0, hup, coe_period, coe_zero]
    · rw [htp, hu0, coe_period, coe_zero]

end AddCircle
