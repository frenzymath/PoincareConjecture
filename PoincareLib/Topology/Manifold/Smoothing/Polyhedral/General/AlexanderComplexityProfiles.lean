import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderComplexityPresentation
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.AlexanderComplexityLevelCharge
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderComplexitySum

/-!
# Complete target profiles and their strict Alexander decrease

Actual nonzero finite PL level comparisons and the checked selected
zero sections supply presentations at every real height. Their charge
profiles have finite support and strictly smaller totals over their own
supports. See Alexander 1924, pp. 6--8 and M76 derivation 246.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Full original polygon families, the actual nonzero level
comparisons or independently verified regular target levels produce
complete target charge profiles. The regular alternative includes
new first-type birth levels of an ordinary cap. A strict selected-plane
decrease implies finite target support and strict total decrease.
The same charge functions retain their prescribed zero values
and the combined bound at every height. See Alexander pp. 6--8
and M76 derivations 246 and 269. -/
theorem exists_decreasing_cut_level_charge_profiles_of_regular_alternatives_with_level_bounds
    {s₀ s₁ T₀ T₁ : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (A : E →ᵃ[ℝ] ℝ) (hcut : s₀ ∩ s₁ ⊆ {x | A x = 0})
    (m : ℝ → ℕ) (n : ∀ c, Fin (m c) → ℕ)
    (P : ∀ c i, Polygon E (n c i + 3)) (r : ℝ → Set E)
    (hP : ∀ c i, Function.Injective (P c i) ∧ (P c i).HasSimplicialEdges)
    (hr : ∀ c, (r c).Subsingleton)
    (hcover : ∀ c, (s₀ ∪ s₁) ∩ {x | A x = c} = r c ∪ ⋃ i, (P c i).boundary ℝ)
    (hpair : ∀ c, Pairwise (fun i j => (P c i).boundary ℝ ∩ (P c j).boundary ℝ ⊆ r c))
    (hfinite : (Function.support
      (fun c => alexanderCurveCount (fun i => (P c i).boundary ℝ))).Finite)
    (hlevels : ∀ c : ℝ, c ≠ 0 →
      (HasAlexanderCurvePresentation (T₀ ∩ {x | A x = c}) 0 ∧
        HasAlexanderCurvePresentation (T₁ ∩ {x | A x = c}) 0) ∨
      ((∃ F : (s₀ ∩ {x | A x = c} : Set E) ≃ₜ (T₀ ∩ {x | A x = c} : Set E),
        F.IsFinitePL) ∧
       (∃ F : (s₁ ∩ {x | A x = c} : Set E) ≃ₜ (T₁ ∩ {x | A x = c} : Set E),
        F.IsFinitePL)))
    (a₀ a₁ : ℕ) (hzero₀ : HasAlexanderCurvePresentation (T₀ ∩ {x | A x = 0}) a₀)
    (hzero₁ : HasAlexanderCurvePresentation (T₁ ∩ {x | A x = 0}) a₁)
    (hzero : a₀ + a₁ < alexanderCurveCount (fun i => (P 0 i).boundary ℝ)) :
    ∃ a b : ℝ → ℕ,
      (∀ c, HasAlexanderCurvePresentation (T₀ ∩ {x | A x = c}) (a c)) ∧
      (∀ c, HasAlexanderCurvePresentation (T₁ ∩ {x | A x = c}) (b c)) ∧
      ∃ ha : (Function.support a).Finite, ∃ hb : (Function.support b).Finite,
        (∑ c ∈ ha.toFinset, a c) + (∑ c ∈ hb.toFinset, b c) <
            ∑ c ∈ hfinite.toFinset, alexanderCurveCount (fun i => (P c i).boundary ℝ) ∧
          (∑ c ∈ ha.toFinset, a c) <
            ∑ c ∈ hfinite.toFinset, alexanderCurveCount (fun i => (P c i).boundary ℝ) ∧
          (∑ c ∈ hb.toFinset, b c) <
            ∑ c ∈ hfinite.toFinset, alexanderCurveCount (fun i => (P c i).boundary ℝ) ∧
          a 0 = a₀ ∧ b 0 = a₁ ∧
          ∀ c, a c + b c ≤ alexanderCurveCount (fun i => (P c i).boundary ℝ) := by
  classical
  have hex (c : ℝ) : ∃ a b : ℕ,
      HasAlexanderCurvePresentation (T₀ ∩ {x | A x = c}) a ∧
      HasAlexanderCurvePresentation (T₁ ∩ {x | A x = c}) b ∧
      a + b ≤ alexanderCurveCount (fun i => (P c i).boundary ℝ) ∧
      (c = 0 → a + b < alexanderCurveCount (fun i => (P c i).boundary ℝ)) ∧
      (c = 0 → a = a₀ ∧ b = a₁) := by
    by_cases hc : c = 0
    · subst c
      exact ⟨a₀, a₁, hzero₀, hzero₁, hzero.le, fun _ => hzero, fun _ => ⟨rfl, rfl⟩⟩
    · rcases hlevels c hc with hregular | hcomparison
      · exact ⟨0, 0, hregular.1, hregular.2, Nat.zero_le _,
          fun h => (hc h).elim, fun h => (hc h).elim⟩
      · obtain ⟨⟨e₀, he₀⟩, ⟨e₁, he₁⟩⟩ := hcomparison
        obtain ⟨I, f₀, f₁, N₀, Q₀, N₁, Q₁, _, _, hQ₀, hQ₁,
            hcover₀, hcover₁, hpair₀, hpair₁, hbound⟩ :=
          Polygon.exists_nonzero_cut_level_charge_bound (n c) (P c)
            (fun i => (hP c i).2) (fun i => (hP c i).1)
            hs₀ hs₁ A hcut hc (hcover c) (hpair c) e₀ he₀ e₁ he₁
        refine ⟨alexanderCurveCount (fun i => (Q₀ i).boundary ℝ),
          alexanderCurveCount (fun i => (Q₁ i).boundary ℝ), ?_, ?_, hbound,
          (fun h => (hc h).elim), (fun h => (hc h).elim)⟩
        · exact hasAlexanderCurvePresentation_of_family N₀ Q₀
            (fun i => ⟨(hQ₀ i).1, (hQ₀ i).2.1⟩)
            (((hr c).anti (inter_subset_left : r c ∩ s₀ ⊆ r c)).image f₀) hcover₀ hpair₀
        · exact hasAlexanderCurvePresentation_of_family N₁ Q₁
            (fun i => ⟨(hQ₁ i).1, (hQ₁ i).2.1⟩)
            (((hr c).anti (inter_subset_left : r c ∩ s₁ ⊆ r c)).image f₁) hcover₁ hpair₁
  choose a b ha hb hbound hstrict hzeroValues using hex
  obtain ⟨hfa, hfb, hsum, hsum₀, hsum₁⟩ := Nat.finite_support_pair_decrease
    (fun c => alexanderCurveCount (fun i => (P c i).boundary ℝ)) a b hfinite
    hbound 0 (hstrict 0 rfl)
  exact ⟨a, b, ha, hb, hfa, hfb, hsum, hsum₀, hsum₁,
    (hzeroValues 0 rfl).1, (hzeroValues 0 rfl).2, hbound⟩

/-- Complete source families and actual level alternatives
give strictly decreasing complete target charge profiles.
This projects the stronger construction retaining every
pointwise bound and both prescribed zero charges. See
Alexander pp. 6--8 and M76 derivations 246 and 269. -/
theorem exists_decreasing_cut_level_charge_profiles_of_regular_alternatives
    {s₀ s₁ T₀ T₁ : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (A : E →ᵃ[ℝ] ℝ) (hcut : s₀ ∩ s₁ ⊆ {x | A x = 0})
    (m : ℝ → ℕ) (n : ∀ c, Fin (m c) → ℕ)
    (P : ∀ c i, Polygon E (n c i + 3)) (r : ℝ → Set E)
    (hP : ∀ c i, Function.Injective (P c i) ∧ (P c i).HasSimplicialEdges)
    (hr : ∀ c, (r c).Subsingleton)
    (hcover : ∀ c, (s₀ ∪ s₁) ∩ {x | A x = c} = r c ∪ ⋃ i, (P c i).boundary ℝ)
    (hpair : ∀ c, Pairwise (fun i j => (P c i).boundary ℝ ∩ (P c j).boundary ℝ ⊆ r c))
    (hfinite : (Function.support
      (fun c => alexanderCurveCount (fun i => (P c i).boundary ℝ))).Finite)
    (hlevels : ∀ c : ℝ, c ≠ 0 →
      (HasAlexanderCurvePresentation (T₀ ∩ {x | A x = c}) 0 ∧
        HasAlexanderCurvePresentation (T₁ ∩ {x | A x = c}) 0) ∨
      ((∃ F : (s₀ ∩ {x | A x = c} : Set E) ≃ₜ (T₀ ∩ {x | A x = c} : Set E),
        F.IsFinitePL) ∧
       (∃ F : (s₁ ∩ {x | A x = c} : Set E) ≃ₜ (T₁ ∩ {x | A x = c} : Set E),
        F.IsFinitePL)))
    (a₀ a₁ : ℕ) (hzero₀ : HasAlexanderCurvePresentation (T₀ ∩ {x | A x = 0}) a₀)
    (hzero₁ : HasAlexanderCurvePresentation (T₁ ∩ {x | A x = 0}) a₁)
    (hzero : a₀ + a₁ < alexanderCurveCount (fun i => (P 0 i).boundary ℝ)) :
    ∃ a b : ℝ → ℕ,
      (∀ c, HasAlexanderCurvePresentation (T₀ ∩ {x | A x = c}) (a c)) ∧
      (∀ c, HasAlexanderCurvePresentation (T₁ ∩ {x | A x = c}) (b c)) ∧
      ∃ ha : (Function.support a).Finite, ∃ hb : (Function.support b).Finite,
        (∑ c ∈ ha.toFinset, a c) + (∑ c ∈ hb.toFinset, b c) <
            ∑ c ∈ hfinite.toFinset, alexanderCurveCount (fun i => (P c i).boundary ℝ) ∧
          (∑ c ∈ ha.toFinset, a c) <
            ∑ c ∈ hfinite.toFinset, alexanderCurveCount (fun i => (P c i).boundary ℝ) ∧
          (∑ c ∈ hb.toFinset, b c) <
            ∑ c ∈ hfinite.toFinset, alexanderCurveCount (fun i => (P c i).boundary ℝ) := by
  obtain ⟨a, b, hpa, hpb, ha, hb, hsum, hsum₀, hsum₁, _, _, _⟩ :=
    exists_decreasing_cut_level_charge_profiles_of_regular_alternatives_with_level_bounds
      hs₀ hs₁ A hcut m n P r hP hr hcover hpair hfinite hlevels a₀ a₁ hzero₀ hzero₁ hzero
  exact ⟨a, b, hpa, hpb, ha, hb, hsum, hsum₀, hsum₁⟩

/-- Actual finite PL comparisons at every nonzero height and a
strict selected-plane decrease give complete target profiles with
finite support and strictly smaller totals. This is the pointed-cap
specialization. See Alexander pp. 6--8 and derivation 246. -/
theorem exists_decreasing_cut_level_charge_profiles
    {s₀ s₁ T₀ T₁ : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (A : E →ᵃ[ℝ] ℝ) (hcut : s₀ ∩ s₁ ⊆ {x | A x = 0})
    (m : ℝ → ℕ) (n : ∀ c, Fin (m c) → ℕ)
    (P : ∀ c i, Polygon E (n c i + 3)) (r : ℝ → Set E)
    (hP : ∀ c i, Function.Injective (P c i) ∧ (P c i).HasSimplicialEdges)
    (hr : ∀ c, (r c).Subsingleton)
    (hcover : ∀ c, (s₀ ∪ s₁) ∩ {x | A x = c} = r c ∪ ⋃ i, (P c i).boundary ℝ)
    (hpair : ∀ c, Pairwise (fun i j => (P c i).boundary ℝ ∩ (P c j).boundary ℝ ⊆ r c))
    (hfinite : (Function.support
      (fun c => alexanderCurveCount (fun i => (P c i).boundary ℝ))).Finite)
    (hlevels : ∀ c : ℝ, c ≠ 0 →
      (∃ F : (s₀ ∩ {x | A x = c} : Set E) ≃ₜ (T₀ ∩ {x | A x = c} : Set E),
        F.IsFinitePL) ∧
      (∃ F : (s₁ ∩ {x | A x = c} : Set E) ≃ₜ (T₁ ∩ {x | A x = c} : Set E),
        F.IsFinitePL))
    (a₀ a₁ : ℕ) (hzero₀ : HasAlexanderCurvePresentation (T₀ ∩ {x | A x = 0}) a₀)
    (hzero₁ : HasAlexanderCurvePresentation (T₁ ∩ {x | A x = 0}) a₁)
    (hzero : a₀ + a₁ < alexanderCurveCount (fun i => (P 0 i).boundary ℝ)) :
    ∃ a b : ℝ → ℕ,
      (∀ c, HasAlexanderCurvePresentation (T₀ ∩ {x | A x = c}) (a c)) ∧
      (∀ c, HasAlexanderCurvePresentation (T₁ ∩ {x | A x = c}) (b c)) ∧
      ∃ ha : (Function.support a).Finite, ∃ hb : (Function.support b).Finite,
        (∑ c ∈ ha.toFinset, a c) + (∑ c ∈ hb.toFinset, b c) <
            ∑ c ∈ hfinite.toFinset, alexanderCurveCount (fun i => (P c i).boundary ℝ) ∧
          (∑ c ∈ ha.toFinset, a c) <
            ∑ c ∈ hfinite.toFinset, alexanderCurveCount (fun i => (P c i).boundary ℝ) ∧
          (∑ c ∈ hb.toFinset, b c) <
            ∑ c ∈ hfinite.toFinset, alexanderCurveCount (fun i => (P c i).boundary ℝ) :=
  exists_decreasing_cut_level_charge_profiles_of_regular_alternatives hs₀ hs₁ A hcut
    m n P r hP hr hcover hpair hfinite (fun c hc => Or.inr (hlevels c hc))
    a₀ a₁ hzero₀ hzero₁ hzero

end Set
