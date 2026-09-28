import PoincareConjecture.Statements.M62CurveEvolution

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

structure M63C2ShrinkingCurveOn (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (J : Set ℝ) : Prop where
  domain_subset : J ⊆ Set.Icc a b
  periodic : ∀ t ∈ J, Function.Periodic (fun x => c x t) curvePeriod
  spatial_regular : ∀ t ∈ J,
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun x => c x t)
  joint_c1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1
    (fun z : ℝ × ℝ => c z.1 z.2) (Set.univ ×ˢ interior J)
  immersed : ∀ t ∈ J, ∀ x,
    curveVelocity (n := n) (fun y => c y t) x ≠ 0
  continuous : ContinuousOn (fun z : ℝ × ℝ => c z.1 z.2)
    (Set.univ ×ˢ J)
  velocity_continuous : ContinuousOn
    (fun z : ℝ × ℝ =>
      (⟨c z.1 z.2, curveVelocity (n := n) (fun y => c y z.2) z.1⟩ :
        TangentBundle (𝓡 n) M)) (Set.univ ×ˢ J)
  curvature_continuous : ContinuousOn
    (fun z : ℝ × ℝ =>
      (⟨c z.1 z.2, m62CurvatureVector F c z.2 z.1⟩ :
        TangentBundle (𝓡 n) M)) (Set.univ ×ˢ J)
  equation : ∀ t ∈ interior J, ∀ x,
    curveVelocity (n := n) (fun s => c x s) t = m62CurvatureVector F c t x

def M63SmoothShrinkingCurveOn (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (J : Set ℝ) : Prop :=
  M63C2ShrinkingCurveOn F c J ∧
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.1 z.2) (Set.univ ×ˢ interior J)

noncomputable def m63CurvatureJet (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) : (i : ℕ) → (t x : ℝ) → TangentSpace (𝓡 n) (c x t)
  | 0, t, x => m62CurvatureVector F c t x
  | i + 1, t, x => m62SpatialDerivative F c t
      (fun y => m63CurvatureJet F c i t y) x

noncomputable def m63CurvatureJetSquared (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (i : ℕ) (t x : ℝ) : ℝ :=
  (F.metric t).inner (c x t)
    (m63CurvatureJet F c i t x) (m63CurvatureJet F c i t x)

structure M63IntrinsicRegularityOn (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (J : Set ℝ) : Prop where
  interior_jets : ∀ i : ℕ,
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 1
      (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ :
          TangentBundle (𝓡 n) M)) (Set.univ ×ˢ interior J)
  closed_positive_jets : ∀ s T : ℝ, a < s → s ≤ T →
    Set.Icc s T ⊆ J → ∀ i : ℕ,
      ContinuousOn (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ :
          TangentBundle (𝓡 n) M)) (Set.univ ×ˢ Set.Icc s T)

noncomputable def m63ArcLength (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t alpha beta : ℝ) : ℝ :=
  ∫ x in alpha..beta, curveSpeed F c t x

noncomputable def m63ArcTotalCurvature (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t alpha beta : ℝ) : ℝ :=
  ∫ x in alpha..beta, m62Curvature F c t x * curveSpeed F c t x

def M63SmallSubarcs (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t r delta : ℝ) : Prop :=
  ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
    m63ArcLength F c t alpha beta ≤ r →
      m63ArcTotalCurvature F c t alpha beta ≤ delta

def M63IsRampAt {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference)
    (gamma : ℝ → P.charts.Point) (t : ℝ) : Prop :=
  ∀ x : ℝ, 0 < m62Slope P (fun y _ => gamma y) t x

noncomputable def m63CanonicalRamp {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (gamma : ℝ → M) (x : ℝ) : P.charts.Point :=
  (gamma x, P.circle.quotient (circumference * x / curvePeriod))

structure M63PositiveDegreeLift {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (gamma : ℝ → P.charts.Point) where
  lift : ℝ → ℝ
  regular : ContDiff ℝ 2 lift
  degree : ℕ
  degree_positive : 0 < degree
  quotient_eq : ∀ x, P.circle.quotient (lift x) = (gamma x).2
  period_shift : ∀ x,
    lift (x + curvePeriod) = lift x + (degree : ℝ) * circumference
  derivative_positive : ∀ x, 0 < deriv lift x

end PoincareConjecture
