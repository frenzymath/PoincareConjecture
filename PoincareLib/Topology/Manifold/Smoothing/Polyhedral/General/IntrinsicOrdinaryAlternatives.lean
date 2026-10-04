import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.IntrinsicRegularOperations

/-!
# Joint level alternatives from intrinsic ordinary birth bands

Opposite ordinary deformations have disjoint signed birth
intervals. The unchanged side there is a PL image of a regular
closed cut, so both targets have zero charge. Every remaining
nonzero level retains both comparisons. See Alexander 1924,
p. 7 and M76 derivation 266.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Intrinsic regular source bands and the two actual
ordinary comparisons yield a joint alternative at every
nonzero height. All level sets are literal carriers for the
same two targets. See Alexander p. 7 and M76 derivation 266. -/
theorem ordinary_joint_level_alternatives
    {S s s' T T' : Set E} {A : E → ℝ} (hA : Continuous A)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {x | A x = 0}) {t u : ℝ}
    (hregularPos : ∀ c ∈ Ioo (0 : ℝ) t,
      HasDisjointPolygonPresentation (S ∩ {x | A x = c}))
    (hregularNeg : ∀ c ∈ Ioo (-u) (0 : ℝ),
      HasDisjointPolygonPresentation (S ∩ {x | A x = c}))
    (hlowPos : ∀ c ∈ Ioo (0 : ℝ) t,
      HasAlexanderCurvePresentation (T ∩ {x | A x = c}) 0)
    (hlowNeg : ∀ c ∈ Ioo (-u) (0 : ℝ),
      HasAlexanderCurvePresentation (T' ∩ {x | A x = c}) 0)
    (hcomparePos : ∀ c : ℝ, c < 0 ∨ t ≤ c →
      ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ (T ∩ {x | A x = c} : Set E),
        F.IsFinitePL)
    (hcompareNeg : ∀ c : ℝ, 0 < c ∨ c ≤ -u →
      ∃ F : (s' ∩ {x | A x = c} : Set E) ≃ₜ (T' ∩ {x | A x = c} : Set E),
        F.IsFinitePL) :
    ∀ c : ℝ, c ≠ 0 →
      (HasAlexanderCurvePresentation (T ∩ {x | A x = c}) 0 ∧
        HasAlexanderCurvePresentation (T' ∩ {x | A x = c}) 0) ∨
      ((∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ (T ∩ {x | A x = c} : Set E),
          F.IsFinitePL) ∧
        (∃ F : (s' ∩ {x | A x = c} : Set E) ≃ₜ (T' ∩ {x | A x = c} : Set E),
          F.IsFinitePL)) := by
  intro c hc
  by_cases hpos : 0 < c
  · by_cases hct : c < t
    · refine Or.inl ⟨hlowPos c ⟨hpos, hct⟩, ?_⟩
      obtain ⟨F, hF⟩ := hcompareNeg c (Or.inl hpos)
      have hreg := ((hregularPos c ⟨hpos, hct⟩).cut_level
        hs hs' hA hunion hcut hc).2
      exact (hreg.of_finitePL F hF).hasAlexanderCurvePresentation
    · exact Or.inr ⟨hcomparePos c (Or.inr (not_lt.mp hct)),
        hcompareNeg c (Or.inl hpos)⟩
  · have hneg : c < 0 := lt_of_le_of_ne (not_lt.mp hpos) hc
    by_cases hcu : -u < c
    · refine Or.inl ⟨?_, hlowNeg c ⟨hcu, hneg⟩⟩
      obtain ⟨F, hF⟩ := hcomparePos c (Or.inl hneg)
      have hreg := ((hregularNeg c ⟨hcu, hneg⟩).cut_level
        hs hs' hA hunion hcut hc).1
      exact (hreg.of_finitePL F hF).hasAlexanderCurvePresentation
    · exact Or.inr ⟨hcomparePos c (Or.inl hneg),
        hcompareNeg c (Or.inr (not_lt.mp hcu))⟩

end Set
