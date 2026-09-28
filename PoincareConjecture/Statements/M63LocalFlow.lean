import PoincareConjecture.Definitions.M63Polygon

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

structure M63LocalCurveTheory (F : RicciFlow n M (Set.Icc a b)) : Prop where
  local_existence : ∀ gamma : ℝ → M,
    Function.Periodic gamma curvePeriod →
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma →
    (∀ x, curveVelocity (n := n) gamma x ≠ 0) →
      ∃ T : ℝ, a < T ∧ T ≤ b ∧ ∃ c : ℝ → ℝ → M,
        M63C2ShrinkingCurveOn F c (Set.Icc a T) ∧
        (∀ x, c x a = gamma x) ∧
        M63IntrinsicRegularityOn F c (Set.Icc a T)
  smooth_local_existence : ∀ gamma : ℝ → M,
    Function.Periodic gamma curvePeriod →
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma →
    (∀ x, curveVelocity (n := n) gamma x ≠ 0) →
      ∃ T : ℝ, a < T ∧ T ≤ b ∧ ∃ c : ℝ → ℝ → M,
        M63SmoothShrinkingCurveOn F c (Set.Icc a T) ∧
        (∀ x, c x a = gamma x) ∧
        M63IntrinsicRegularityOn F c (Set.Icc a T)
  unique_closed : ∀ (T : ℝ), a < T → T ≤ b →
    ∀ c d : ℝ → ℝ → M,
      M63C2ShrinkingCurveOn F c (Set.Icc a T) →
      M63C2ShrinkingCurveOn F d (Set.Icc a T) →
      (∀ x, c x a = d x a) →
        ∀ t ∈ Set.Icc a T, ∀ x, c x t = d x t
  unique_half_open : ∀ (T : ℝ), a < T → T ≤ b →
    ∀ c d : ℝ → ℝ → M,
      M63C2ShrinkingCurveOn F c (Set.Ico a T) →
      M63C2ShrinkingCurveOn F d (Set.Ico a T) →
      (∀ x, c x a = d x a) →
        ∀ t ∈ Set.Ico a T, ∀ x, c x t = d x t
  intrinsic_regularity : ∀ (T : ℝ), a < T → T ≤ b →
    ∀ (J : Set ℝ), (J = Set.Icc a T ∨ J = Set.Ico a T) →
      ∀ c : ℝ → ℝ → M, M63C2ShrinkingCurveOn F c J →
        M63IntrinsicRegularityOn F c J
  smooth_initial_upgrade : ∀ (T : ℝ), a < T → T ≤ b →
    ∀ (J : Set ℝ), (J = Set.Icc a T ∨ J = Set.Ico a T) →
      ∀ c : ℝ → ℝ → M, M63C2ShrinkingCurveOn F c J →
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c x a) →
          M63SmoothShrinkingCurveOn F c J
  continuation : ∀ (T : ℝ), a < T → T ≤ b →
    ∀ (c : ℝ → ℝ → M), M63C2ShrinkingCurveOn F c (Set.Ico a T) →
      ∀ (K : ℝ), 0 ≤ K →
        (∀ t ∈ Set.Ico a T, ∀ x, m62Curvature F c t x ≤ K) →
          ∃ T' : ℝ, T ≤ T' ∧ T' ≤ b ∧ (T < b → T < T') ∧
            ∃ d : ℝ → ℝ → M,
              M63C2ShrinkingCurveOn F d (Set.Icc a T') ∧
              ∀ t ∈ Set.Ico a T, ∀ x, d x t = c x t
  continuous_dependence : ∀ (Z : Type u) [TopologicalSpace Z] [CompactSpace Z]
    (gamma : Z → ℝ → M),
    Continuous (fun z : Z × ℝ => gamma z.1 z.2) →
    Continuous (fun z : Z × ℝ => m63AngularFirstJet (n := n) (gamma z.1) z.2) →
    Continuous (fun z : Z × ℝ =>
      m63AngularSecondJet (F.connection a) (gamma z.1) z.2) →
    (∀ z, Function.Periodic (gamma z) curvePeriod) →
    (∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gamma z)) →
    (∀ z x, curveVelocity (n := n) (gamma z) x ≠ 0) →
      ∃ T : ℝ, a < T ∧ T ≤ b ∧ ∃ c : Z → ℝ → ℝ → M,
        (∀ z, M63C2ShrinkingCurveOn F (c z) (Set.Icc a T)) ∧
        (∀ z x, c z x a = gamma z x) ∧
        (∀ z, M63IntrinsicRegularityOn F (c z) (Set.Icc a T)) ∧
        Continuous (fun z : (Z × ℝ) × Set.Icc a T => c z.1.1 z.1.2 z.2) ∧
        Continuous (fun z : (Z × ℝ) × Set.Icc a T =>
          m63AngularFirstJet (n := n) (fun x => c z.1.1 x z.2) z.1.2) ∧
        Continuous (fun z : (Z × ℝ) × Set.Icc a T =>
          m63AngularSecondJet (F.connection z.2)
            (fun x => c z.1.1 x z.2) z.1.2)
  fixed_relabeling : ∀ (T : ℝ), a < T → T ≤ b →
    ∀ (J : Set ℝ), (J = Set.Icc a T ∨ J = Set.Ico a T) →
      ∀ (c : ℝ → ℝ → M), M63C2ShrinkingCurveOn F c J →
        ∀ (tau s : ℝ), a < tau → tau < s → s ≤ T → Set.Icc tau s ⊆ J →
          ∃ (phi : ℝ → ℝ) (d : ℝ → ℝ → M),
            ContDiff ℝ 2 phi ∧ Function.Bijective phi ∧
            (∀ x, 0 < deriv phi x) ∧
            (∀ x, phi (x + curvePeriod) = phi x + curvePeriod) ∧
            M63SmoothShrinkingCurveOn F d (Set.Icc tau s) ∧
            (∀ t ∈ Set.Icc tau s,
              ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => d x t)) ∧
            ∀ t ∈ Set.Icc tau s, ∀ x, c x t = d (phi x) t

end PoincareConjecture
