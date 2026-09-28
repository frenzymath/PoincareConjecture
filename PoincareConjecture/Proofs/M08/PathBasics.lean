import PoincareConjecture.Definitions.Ch06.LGeometry
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem reducedLength_eq_of_minimizing {J : Set ℝ} {F : RicciFlow n M J}
    {T τ : ℝ} {p q : M} (path : BackwardTimePath F T 0 τ)
    (hp : path.curve 0 = p) (hq : path.curve τ = q)
    (hmin : IsMinimizingBackwardLPath F T 0 τ path) :
    reducedLength F T p q τ =
      backwardLLength F T 0 τ path.curve / (2 * Real.sqrt τ) := by
  have hleast : IsLeast {L : ℝ |
      ∃ other : BackwardTimePath F T 0 τ,
        other.curve 0 = p ∧ other.curve τ = q ∧
          L = backwardLLength F T 0 τ other.curve}
      (backwardLLength F T 0 τ path.curve) := by
    refine ⟨⟨path, hp, hq, rfl⟩, ?_⟩
    rintro L ⟨other, hleft, hright, rfl⟩
    exact hmin other (hleft.trans hp.symm) (hright.trans hq.symm)
  simp only [reducedLength, dif_pos path.ordered, hleast.csInf_eq]

theorem reducedLength_attained_of_exists_minimizing {J : Set ℝ} {F : RicciFlow n M J}
    {T τ : ℝ} {p q : M}
    (h : ∃ path : BackwardTimePath F T 0 τ,
      path.curve 0 = p ∧ path.curve τ = q ∧
        IsMinimizingBackwardLPath F T 0 τ path) :
    ∃ path : BackwardTimePath F T 0 τ,
      path.curve 0 = p ∧ path.curve τ = q ∧
        IsMinimizingBackwardLPath F T 0 τ path ∧
        reducedLength F T p q τ =
          backwardLLength F T 0 τ path.curve / (2 * Real.sqrt τ) := by
  obtain ⟨path, hp, hq, hmin⟩ := h
  exact ⟨path, hp, hq, hmin, reducedLength_eq_of_minimizing path hp hq hmin⟩

def variationSqrtRegularPath {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) : SqrtRegularPath p where
  curve := V.baseSquareCurve
  domain := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
  open_domain := V.square_open.preimage (continuous_id.prodMk continuous_const)
  interval_subset := by
    intro s hs
    exact V.square_contains ⟨hs, neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  smooth := V.square_smooth.comp
    (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hs ↦ hs)
  agrees := by
    intro s hs
    exact (V.square_agrees s hs 0
      ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩).trans (V.at_zero (s ^ 2))

theorem backwardTime_mem_window {T τmax τ₁ τ₂ τ : ℝ}
    (hτ₁ : 0 ≤ τ₁) (hτ₂ : τ₂ ≤ τmax) (hτ : τ ∈ Set.Icc τ₁ τ₂) :
    T - τ ∈ Set.Icc (T - τmax) T :=
  ⟨sub_le_sub_left (hτ.2.trans hτ₂) T, sub_le_self T (hτ₁.trans hτ.1)⟩

theorem backwardPath_metric_comparison {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ K : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hτ₁ : 0 ≤ τ₁) (hordered : τ₁ ≤ τ₂) (hτ₂ : τ₂ ≤ τmax)
    (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Set.Icc (T - τmax) T, ∀ x : M,
      |(F.connection t).curvatureTensorNorm x| ≤ K)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    Real.exp (-2 * (n : ℝ) * K * (τ₂ - τ₁)) *
        (F.metric (T - τ₂)).inner x v v ≤ (F.metric (T - τ₁)).inner x v v ∧
      (F.metric (T - τ₁)).inner x v v ≤
        Real.exp (2 * (n : ℝ) * K * (τ₂ - τ₁)) *
          (F.metric (T - τ₂)).inner x v v := by
  have hleft : T - τ₂ ∈ Set.Icc (T - τmax) T :=
    backwardTime_mem_window hτ₁ hτ₂ ⟨hordered, le_rfl⟩
  have hright : T - τ₁ ∈ Set.Icc (T - τmax) T :=
    backwardTime_mem_window hτ₁ hτ₂ ⟨le_rfl, hordered⟩
  have hdelta : T - τ₁ - (T - τ₂) = τ₂ - τ₁ := by ring
  have hcomparison := hM04.metric_comparison n M J F (T - τ₂) (T - τ₁) K
    (hwindow hleft) (hwindow hright) (sub_le_sub_left hordered T) hK
    (fun t ht x ↦ (le_abs_self _).trans
      (hbound t ⟨hleft.1.trans ht.1, ht.2.trans hright.2⟩ x)) x v
  simpa only [hdelta] using hcomparison

end PoincareConjecture.M08
