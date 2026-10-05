import PoincareLib.Geometry.CurveShortening.Evolution.CorrectedTheory

/-!
# Primitive curves, intrinsic derivatives and ramps for M63

Morgan--Tian Claim 19.1, Definition 19.12 and Lemmas 19.14/19.24, with
the 2015 Section 19.2 correction, pp. 8-9. The curve and every derivative
are computed in the same actual ambient Ricci flow. General C2 parameter
labels are retained; the smooth branch is a separate primitive property.
Existence, regularity and estimates are conclusions of the M63 milestone.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- A displayed C2 immersed solution on its actual time set. Analytic
statements use nontrivial closed or half-open intervals within the flow slab. -/
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

/-- Smoothness of the same parameterized solution on the open time slab.
This additional property is not required of arbitrary C2 initial labels. -/
def M63SmoothShrinkingCurveOn (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (J : Set ℝ) : Prop :=
  M63C2ShrinkingCurveOn F c J ∧
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.1 z.2) (Set.univ ×ˢ interior J)

/-- The actual recursive spatial covariant derivative `D_s^i H`, with order
zero equal to the curvature vector rather than the unit tangent. -/
noncomputable def m63CurvatureJet (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) : (i : ℕ) → (t x : ℝ) → TangentSpace (𝓡 n) (c x t)
  | 0, t, x => m62CurvatureVector F c t x
  | i + 1, t, x => m62SpatialDerivative F c t
      (fun y => m63CurvatureJet F c i t y) x

noncomputable def m63CurvatureJetSquared (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (i : ℕ) (t x : ℝ) : ℝ :=
  (F.metric t).inner (c x t)
    (m63CurvatureJet F c i t x) (m63CurvatureJet F c i t x)

/-- Positive-time regularity of the actual intrinsic jets. It includes the
final endpoint on every included positive closed slab, but imposes no higher
jet regularity at the original C2 initial slice. -/
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

/-- Length of an actual parameter subarc in the evolving metric. -/
noncomputable def m63ArcLength (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t alpha beta : ℝ) : ℝ :=
  ∫ x in alpha..beta, curveSpeed F c t x

/-- Total curvature of the same parameter subarc. -/
noncomputable def m63ArcTotalCurvature (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t alpha beta : ℝ) : ℝ :=
  ∫ x in alpha..beta, m62Curvature F c t x * curveSpeed F c t x

/-- The local small-total-curvature hypothesis in Lemma 19.24, tested on
every parameter subarc of at most one period whose metric length is at most r. -/
def M63SmallSubarcs (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t r delta : ℝ) : Prop :=
  ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
    m63ArcLength F c t alpha beta ≤ r →
      m63ArcTotalCurvature F c t alpha beta ≤ delta

/-- Positive slope against the actual fixed unit circle field. Regularity
and periodicity are separate hypotheses, and arbitrary positive degree is allowed. -/
def M63IsRampAt {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference)
    (gamma : ℝ → P.charts.Point) (t : ℝ) : Prop :=
  ∀ x : ℝ, 0 < m62Slope P (fun y _ => gamma y) t x

/-- The exact degree-one graph over a base loop, with the last coordinate
measured in circle arc length. -/
noncomputable def m63CanonicalRamp {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (gamma : ℝ → M) (x : ℝ) : P.charts.Point :=
  (gamma x, P.circle.quotient (circumference * x / curvePeriod))

/-- An actual increasing C2 lift of the circle projection and its positive
winding degree. Existence of this certificate is a conclusion for a ramp. -/
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

end PoincareMT
