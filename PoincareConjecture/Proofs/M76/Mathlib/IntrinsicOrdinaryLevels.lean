import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularOperations

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem ordinary_capped_low_level_presentations
    {S s s' b d : Set E} {A : E → ℝ} (hA : Continuous A)
    (hs : IsClosed s) (hs' : IsClosed s')
    (hunion : s ∪ s' = S) (hinter : s ∩ s' ⊆ {x | A x = 0})
    (hb : IsCompact b) {t : ℝ} (ht : 0 < t) (H : E → E) (p : E)
    (hregular : ∀ c ∈ Ioo (0 : ℝ) t,
      HasDisjointPolygonPresentation (S ∩ {x | A x = c}))
    (hminimum : (H '' d) ∩ {x | A x = t * (2 / 3)} = {H p})
    (hempty : ∀ c : ℝ, c < t * (2 / 3) ∨ t < c → (H '' d) ∩ {x | A x = c} = ∅)
    (hdisks : ∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
      IsFinitePLBallPair (ℝ × ℝ) ((H '' d) ∩ {x | A x ≤ t * a})
        ((H '' d) ∩ {x | A x = t * a}))
    (hlow : ∀ c ∈ Ioo (0 : ℝ) t,
      ∃ (Z : Set E) (f : E → E) (X Y : Set E),
        FinitePiecewiseAffineOn f Z ∧ InjOn f Z ∧ b ⊆ Z ∧
        s ∩ {x | A x = c} = (f '' b) ∪ X ∧ Disjoint (f '' b) X ∧
        (H '' (s ∪ d)) ∩ {x | A x = c} = ((H '' d) ∩ {x | A x = c}) ∪ Y ∧
        Disjoint ((H '' d) ∩ {x | A x = c}) Y ∧ ∃ F : X ≃ₜ Y, F.IsFinitePL) :
    ∀ c ∈ Ioo (0 : ℝ) t,
      HasAlexanderCurvePresentation ((H '' (s ∪ d)) ∩ {x | A x = c}) 0 ∧
        (c ≠ t * (2 / 3) →
          HasDisjointPolygonPresentation ((H '' (s ∪ d)) ∩ {x | A x = c})) := by
  intro c hc
  have hcut := ((hregular c hc).cut_level hs hs' hA hunion hinter hc.1.ne').1
  obtain ⟨Z, f, X, Y, hf, _, hbZ, hsource, hsep, htarget, hcapSep, F, hF⟩ := hlow c hc
  have hbClosed : IsClosed (f '' b) :=
    (hb.image_of_continuousOn (hf.continuousOn.mono hbZ)).isClosed
  rw [hsource] at hcut
  have hY := hcut.finitePL_remainder hbClosed hsep F hF
  rw [htarget]
  rcases lt_trichotomy c (t * (2 / 3)) with hbelow | heq | habove
  · have hregular := hY.union_regular_cap (Or.inl (hempty c (Or.inl hbelow))) hcapSep
    exact ⟨hregular.hasAlexanderCurvePresentation, fun _ => hregular⟩
  · refine ⟨?_, fun hne => (hne heq).elim⟩
    obtain ⟨m, n, P, hP, hcover, hpair⟩ := hY
    apply hasAlexanderCurvePresentation_zero_union_cap n P hP hpair hcover
      (Or.inl ?_) hcapSep
    rw [heq, hminimum]
    exact subsingleton_singleton
  · have hratio : c / t ∈ Ioc (2 / 3) 1 := by
      constructor
      · apply (lt_div_iff₀ ht).mpr
        nlinarith
      · exact (div_le_one ht).mpr hc.2.le
    have htc : t * (c / t) = c := by field_simp [ht.ne']
    have hball : IsFinitePLBallPair (ℝ × ℝ) ((H '' d) ∩ {x | A x ≤ c})
        ((H '' d) ∩ {x | A x = c}) := by
      simpa only [htc] using hdisks (c / t) hratio
    have hregular := hY.union_regular_cap (Or.inr ⟨_, hball⟩) hcapSep
    exact ⟨hregular.hasAlexanderCurvePresentation, fun _ => hregular⟩

end Set
