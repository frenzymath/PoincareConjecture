import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegularProfileSections
import PoincareConjecture.Proofs.M76.Mathlib.FinitePositiveHeightGap
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderCollarWidthRestriction











set_option autoImplicit false

open Set Geometry

namespace Geometry.AlexanderSectionProfile

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem exists_regular_section_window
    (W : AlexanderSectionProfile E) {D : Set F}
    {e : W.carrier ≃ₜ frontier D} (he : e.IsFinitePL)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hdim : Module.finrank ℝ F = 3) {C : Set ℝ} (hC : C.Finite)
    (hsigns : ∀ x ∈ W.carrier, W.height x ∉ C →
      x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
        x ∈ closure (W.carrier ∩ {y | W.height x < W.height y}))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, η ∈ Ioo 0 ε ∧
      (∀ c ∈ Ioo (-η) η, c ≠ 0 → c ∉ C ∪ Function.support W.charge) ∧
      (∀ c ∈ Ioo (0 : ℝ) η,
        HasDisjointPolygonPresentation (W.carrier ∩ {x | W.height x = c})) ∧
      (∀ c ∈ Ioo (0 : ℝ) η,
        HasDisjointPolygonPresentation (W.carrier ∩ {x | (-W.height) x = c})) ∧
      ∀ x ∈ W.carrier, W.height x ∈ Ioo (-η) η → W.height x ≠ 0 →
        x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
          x ∈ closure (W.carrier ∩ {y | W.height x < W.height y}) := by
  obtain ⟨hevents, hregular⟩ :=
    W.finite_exceptional_regular_sections he hD hcv hne hdim hC hsigns
  obtain ⟨η, hη, hgap⟩ := hevents.exists_pos_lt_positive_values
    (fun c : ℝ => |c|) hε
  have havoid (c : ℝ) (hc : c ∈ Ioo (-η) η) (hc0 : c ≠ 0) :
      c ∉ C ∪ Function.support W.charge := by
    intro hcE
    exact lt_asymm (hgap c hcE (abs_pos.mpr hc0)) (abs_lt.mpr hc)
  refine ⟨η, hη, havoid, ?_, ?_, ?_⟩
  · intro c hc
    exact hregular c (havoid c
      ⟨(neg_lt_zero.mpr hη.1).trans hc.1, hc.2⟩ hc.1.ne')
  · intro c hc
    have h := hregular (-c) (havoid (-c)
      ⟨by linarith [hc.2], by linarith [hc.1, hη.1]⟩
      (neg_ne_zero.mpr hc.1.ne'))
    have hsection : W.carrier ∩ {x | (-W.height) x = c} =
        W.carrier ∩ {x | W.height x = -c} := by
      ext x
      change (x ∈ W.carrier ∧ -W.height x = c) ↔
        (x ∈ W.carrier ∧ W.height x = -c)
      constructor <;> rintro ⟨hx, hxA⟩ <;> exact ⟨hx, by linarith⟩
    rw [hsection]
    exact h
  · intro x hx hxA hx0
    exact hsigns x hx (fun hc => havoid _ hxA hx0 (Or.inl hc))






theorem exists_regular_collared_section_window
    (W : AlexanderSectionProfile E) {D : Set F}
    {e : W.carrier ≃ₜ frontier D} (he : e.IsFinitePL)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hdim : Module.finrank ℝ F = 3) {C : Set ℝ} (hC : C.Finite)
    (hsigns : ∀ x ∈ W.carrier, W.height x ∉ C →
      x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
        x ∈ closure (W.carrier ∩ {y | W.height x < W.height y}))
    {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab W.carrier W.height q β)
    (Mneg : AlexanderCollarSlab W.carrier (-W.height) q γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, η ∈ Ioo 0 ε ∧
      ∃ N : AlexanderCollarSlab W.carrier W.height q η,
      ∃ Nneg : AlexanderCollarSlab W.carrier (-W.height) q η,
        N.upper = (fun x => min (M.upper x) η) ∧
        N.collar = M.collar ∩ {x | W.height x ∈ Icc 0 η} ∧
        N.residual = (M.residual ∩ {x | W.height x ∈ Icc 0 η}) ∪
          (W.carrier ∩ {x | W.height x = η}) ∧
        Nneg.upper = (fun x => min (Mneg.upper x) η) ∧
        Nneg.collar = Mneg.collar ∩ {x | (-W.height) x ∈ Icc 0 η} ∧
        Nneg.residual = (Mneg.residual ∩ {x | (-W.height) x ∈ Icc 0 η}) ∪
          (W.carrier ∩ {x | (-W.height) x = η}) ∧
        (∀ c ∈ Ioo (-η) η, c ≠ 0 → c ∉ C ∪ Function.support W.charge) ∧
        (∀ c ∈ Ioo (0 : ℝ) η,
          HasDisjointPolygonPresentation (W.carrier ∩ {x | W.height x = c})) ∧
        (∀ c ∈ Ioo (0 : ℝ) η,
          HasDisjointPolygonPresentation (W.carrier ∩ {x | (-W.height) x = c})) ∧
        ∀ x ∈ W.carrier, W.height x ∈ Ioo (-η) η → W.height x ≠ 0 →
          x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
            x ∈ closure (W.carrier ∩ {y | W.height x < W.height y}) := by
  have hbound : 0 < min ε (min β γ) :=
    lt_min hε (lt_min M.width_pos Mneg.width_pos)
  obtain ⟨η, hη, havoid, hregular, hregularNeg, hlocal⟩ :=
    W.exists_regular_section_window he hD hcv hne hdim hC hsigns hbound
  have hηε : η ∈ Ioo 0 ε := ⟨hη.1, hη.2.trans_le (min_le_left _ _)⟩
  have hηβ : η ≤ β :=
    hη.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηγ : η ≤ γ :=
    hη.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨N, hNu, hNc, hNr⟩ := M.exists_width_restriction hη.1 hηβ
  obtain ⟨Nneg, hNnu, hNnc, hNnr⟩ := Mneg.exists_width_restriction hη.1 hηγ
  exact ⟨η, hηε, N, Nneg, hNu, hNc, hNr, hNnu, hNnc, hNnr,
    havoid, hregular, hregularNeg, hlocal⟩

end Geometry.AlexanderSectionProfile
