import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveInduction
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityProfiles

set_option autoImplicit false

open Set

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_decreasing_children_with_level_bounds (P : AlexanderSectionProfile E)
    {s₀ s₁ T₀ T₁ : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (hcarrier : s₀ ∪ s₁ = P.carrier)
    (hcut : s₀ ∩ s₁ ⊆ {x | P.height x = 0})
    (hlevels : ∀ c : ℝ, c ≠ 0 →
      (HasAlexanderCurvePresentation (T₀ ∩ {x | P.height x = c}) 0 ∧
        HasAlexanderCurvePresentation (T₁ ∩ {x | P.height x = c}) 0) ∨
      ((∃ F : (s₀ ∩ {x | P.height x = c} : Set E) ≃ₜ
          (T₀ ∩ {x | P.height x = c} : Set E), F.IsFinitePL) ∧
        (∃ F : (s₁ ∩ {x | P.height x = c} : Set E) ≃ₜ
          (T₁ ∩ {x | P.height x = c} : Set E), F.IsFinitePL)))
    {a₀ a₁ : ℕ} (hzero₀ : HasAlexanderCurvePresentation (T₀ ∩ {x | P.height x = 0}) a₀)
    (hzero₁ : HasAlexanderCurvePresentation (T₁ ∩ {x | P.height x = 0}) a₁)
    (hzero : a₀ + a₁ < P.charge 0) :
    ∃ L R : AlexanderSectionProfile E,
      L.carrier = T₀ ∧ R.carrier = T₁ ∧ L.height = P.height ∧ R.height = P.height ∧
        L.complexity + R.complexity < P.complexity ∧
        L.charge 0 = a₀ ∧ R.charge 0 = a₁ ∧
        (∀ c, L.charge c + R.charge c ≤ P.charge c) ∧
        Function.support L.charge ⊆ Function.support P.charge ∧
        Function.support R.charge ⊆ Function.support P.charge := by
  classical
  have hpres := P.presentation
  choose m n Q r hQ hr hcover hpair hcount using hpres
  let k : ℝ → ℕ := fun c => alexanderCurveCount (fun i => (Q c i).boundary ℝ)
  have hk : k = P.charge := funext hcount
  have hfinite : (Function.support k).Finite := hk.symm ▸ P.finite_support
  have hcover' (c : ℝ) : (s₀ ∪ s₁) ∩ {x | P.height x = c} =
      r c ∪ ⋃ i, (Q c i).boundary ℝ := by
    rw [hcarrier]
    exact hcover c
  have hsum : (∑ c ∈ hfinite.toFinset, k c) = P.complexity := by
    have hsupport : hfinite.toFinset = P.finite_support.toFinset := by
      ext c
      simp only [Set.Finite.mem_toFinset, hk]
    rw [hsupport]
    exact Finset.sum_congr rfl (fun c _ => hcount c)
  obtain ⟨a, b, hpa, hpb, ha, hb, hlt, _, _, ha₀, hb₀, hbound⟩ :=
    exists_decreasing_cut_level_charge_profiles_of_regular_alternatives_with_level_bounds hs₀ hs₁
      P.height hcut m n Q r hQ hr hcover' hpair hfinite hlevels a₀ a₁ hzero₀ hzero₁
      (by rwa [hcount 0])
  let L : AlexanderSectionProfile E :=
    ⟨T₀, P.height, a, hpa, ha⟩
  let R : AlexanderSectionProfile E :=
    ⟨T₁, P.height, b, hpb, hb⟩
  have hpoint (c : ℝ) : L.charge c + R.charge c ≤ P.charge c :=
    (hbound c).trans_eq (hcount c)
  refine ⟨L, R, rfl, rfl, rfl, rfl, ?_, ha₀, hb₀, hpoint, ?_, ?_⟩
  · change (∑ c ∈ ha.toFinset, a c) + (∑ c ∈ hb.toFinset, b c) < P.complexity
    exact hlt.trans_eq hsum
  · intro c hc hz
    have h := hpoint c
    rw [hz] at h
    exact hc (by omega)
  · intro c hc hz
    have h := hpoint c
    rw [hz] at h
    exact hc (by omega)

theorem exists_decreasing_children (P : AlexanderSectionProfile E)
    {s₀ s₁ T₀ T₁ : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (hcarrier : s₀ ∪ s₁ = P.carrier)
    (hcut : s₀ ∩ s₁ ⊆ {x | P.height x = 0})
    (hlevels : ∀ c : ℝ, c ≠ 0 →
      (HasAlexanderCurvePresentation (T₀ ∩ {x | P.height x = c}) 0 ∧
        HasAlexanderCurvePresentation (T₁ ∩ {x | P.height x = c}) 0) ∨
      ((∃ F : (s₀ ∩ {x | P.height x = c} : Set E) ≃ₜ
          (T₀ ∩ {x | P.height x = c} : Set E), F.IsFinitePL) ∧
        (∃ F : (s₁ ∩ {x | P.height x = c} : Set E) ≃ₜ
          (T₁ ∩ {x | P.height x = c} : Set E), F.IsFinitePL)))
    {a₀ a₁ : ℕ} (hzero₀ : HasAlexanderCurvePresentation (T₀ ∩ {x | P.height x = 0}) a₀)
    (hzero₁ : HasAlexanderCurvePresentation (T₁ ∩ {x | P.height x = 0}) a₁)
    (hzero : a₀ + a₁ < P.charge 0) :
    ∃ L R : AlexanderSectionProfile E,
      L.carrier = T₀ ∧ R.carrier = T₁ ∧ L.height = P.height ∧ R.height = P.height ∧
        L.complexity + R.complexity < P.complexity := by
  obtain ⟨L, R, hL, hR, hLA, hRA, hlt, _, _, _, _, _⟩ :=
    P.exists_decreasing_children_with_level_bounds hs₀ hs₁ hcarrier hcut hlevels
      hzero₀ hzero₁ hzero
  exact ⟨L, R, hL, hR, hLA, hRA, hlt⟩

end Geometry.AlexanderSectionProfile
