import PoincareConjecture.Definitions.Ch19.CurveEvolution
import PoincareConjecture.Statements.Ch04.CurvatureTheory

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
variable {t₀ t₁ : ℝ}

structure CurveEvolutionAmbientBounds
    (F : RicciFlow n M (Set.Icc t₀ t₁)) (K₀ K₁ K₂ : ℝ) : Prop where
  riemann : ∀ t ∈ Set.Icc t₀ t₁, ∀ x : M,
    ∀ v : Fin 4 → TangentSpace (𝓡 n) x,
      (∀ i, (F.metric t).tangentNorm x (v i) ≤ 1) →
        |(F.connection t).curvatureTensor x (v 0) (v 1) (v 2) (v 3)| ≤ K₀
  ricci_derivative : ∀ t ∈ Set.Icc t₀ t₁, ∀ x : M,
    ∀ v : Fin 3 → TangentSpace (𝓡 n) x,
      (∀ i, (F.metric t).tangentNorm x (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          (F.connection t).ricciEvaluation x v| ≤ K₁
  ricci : ∀ t ∈ Set.Icc t₀ t₁, ∀ x : M,
    ∀ v w : TangentSpace (𝓡 n) x,
      (F.metric t).tangentNorm x v ≤ 1 → (F.metric t).tangentNorm x w ≤ 1 →
        |(F.connection t).ricci x v w| ≤ K₂

structure CurveEvolutionPredecessors where
  curvature : RicciFlowCurvatureTheory.{u}
  flow : RicciFlow n M (Set.Icc t₀ t₁)
  K₀ : ℝ
  K₁ : ℝ
  K₂ : ℝ
  bounds_nonnegative : 0 ≤ K₀ ∧ 0 ≤ K₁ ∧ 0 ≤ K₂
  bounds : CurveEvolutionAmbientBounds flow K₀ K₁ K₂

structure CurveEvolutionSolution (F : RicciFlow n M (Set.Icc t₀ t₁)) where
  family : CurveShrinkingFlow.Data F
  shrinking_equation : SatisfiesCurveShrinkingEquation family
  curvature_extension : ∀ t : ℝ, SmoothAlongCurveExtensionOn Set.univ
    (fun x ↦ family.curve x t) (fun x ↦ curveCurvatureVector family t x)
  squared_curvature_regular : ∀ t : ℝ,
    ContDiffOn ℝ 2 (fun x ↦ curveCurvatureSquared family t x) Set.univ
  time_squared_curvature_regular : ∀ x : ℝ,
    ContDiffOn ℝ 1 (fun t ↦ curveCurvatureSquared family t x) (Set.Icc t₀ t₁)
  length_integrable : ∀ t : ℝ, IntervalIntegrable
    (fun x ↦ curveSpeed F family.curve t x) MeasureTheory.volume 0 curvePeriod
  curvature_integrable : ∀ t : ℝ, IntervalIntegrable
    (fun x ↦ curveCurvature family t x * curveSpeed F family.curve t x)
    MeasureTheory.volume 0 curvePeriod

noncomputable def correctedCurvatureSquaredRhs
    {F : RicciFlow n M (Set.Icc t₀ t₁)} (S : CurveEvolutionSolution F)
    (C₀ t x : ℝ) : ℝ :=
  arcLengthSecondDerivative S.family t x -
    2 * (F.metric t).inner (S.family.curve x t)
      (normalCovariantDerivative S.family t x (S.curvature_extension t))
      (normalCovariantDerivative S.family t x (S.curvature_extension t)) +
    2 * (curveCurvatureSquared S.family t x) ^ 2 +
    C₀ * (curveCurvatureSquared S.family t x + curveCurvature S.family t x)

noncomputable def regularizedCurveCurvature
    {F : RicciFlow n M (Set.Icc t₀ t₁)} (S : CurveEvolutionSolution F)
    (ε t x : ℝ) : ℝ :=
  Real.sqrt (curveCurvatureSquared S.family t x + ε ^ 2)

noncomputable def regularizedCurveCurvatureRhs
    {F : RicciFlow n M (Set.Icc t₀ t₁)} (S : CurveEvolutionSolution F)
    (C₁ ε t x : ℝ) : ℝ :=
  arcLengthSecondDerivativeOf S.family t
      (fun y ↦ regularizedCurveCurvature S ε t y) x +
    (curveCurvature S.family t x) ^ 3 +
    C₁ * (regularizedCurveCurvature S ε t x + 1)

structure CurveEvolutionEstimates
    {F : RicciFlow n M (Set.Icc t₀ t₁)} (S : CurveEvolutionSolution F)
    (C₀ C₁ C₂ : ℝ) : Prop where
  pointwise_curvature_squared : ∀ t ∈ Set.Ioo t₀ t₁, ∀ x : ℝ,
    deriv (fun s ↦ curveCurvatureSquared S.family s x) t ≤
      correctedCurvatureSquaredRhs S C₀ t x
  regularized_curvature : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo t₀ t₁, ∀ x : ℝ,
    deriv (fun s ↦ regularizedCurveCurvature S ε s x) t ≤
      regularizedCurveCurvatureRhs S C₁ ε t x
  length_identity : ∀ t ∈ Set.Ioo t₀ t₁,
    HasDerivAt (totalCurveLength S.family)
      (-(∫ x in (0 : ℝ)..curvePeriod,
        (curveCurvatureSquared S.family t x +
          (F.connection t).ricci (S.family.curve x t)
            (spatialUnitTangent F S.family.curve t x)
            (spatialUnitTangent F S.family.curve t x)) *
          curveSpeed F S.family.curve t x)) t
  length_derivative_bound : ∀ t ∈ Set.Ioo t₀ t₁,
    deriv (totalCurveLength S.family) t ≤
      ∫ x in (0 : ℝ)..curvePeriod,
        (C₂ - curveCurvatureSquared S.family t x) * curveSpeed F S.family.curve t x
  continuous_length : ContinuousOn (totalCurveLength S.family) (Set.Icc t₀ t₁)
  continuous_total_curvature :
    ContinuousOn (totalCurveCurvature S.family) (Set.Icc t₀ t₁)
  total_curvature_integral :
    ∀ a b : ℝ, a ∈ Set.Icc t₀ t₁ → b ∈ Set.Icc t₀ t₁ → a ≤ b →
      totalCurveCurvature S.family b - totalCurveCurvature S.family a ≤
        ∫ t in a..b, (C₁ + C₂) * totalCurveCurvature S.family t +
          C₁ * totalCurveLength S.family t
  exponential_length_bound :
    ∀ a b : ℝ, a ∈ Set.Icc t₀ t₁ → b ∈ Set.Icc t₀ t₁ → a ≤ b →
      totalCurveLength S.family b ≤
        totalCurveLength S.family a * Real.exp (C₂ * (b - a))
  exponential_total_curvature_bound :
    ∀ a b : ℝ, a ∈ Set.Icc t₀ t₁ → b ∈ Set.Icc t₀ t₁ → a ≤ b →
      totalCurveCurvature S.family b + totalCurveLength S.family b ≤
        (totalCurveCurvature S.family a + totalCurveLength S.family a) *
          Real.exp ((C₁ + C₂) * (b - a))

structure CurveEvolutionConclusions
    (P : CurveEvolutionPredecessors (n := n) (M := M) (t₀ := t₀) (t₁ := t₁)) where
  C₀ : ℝ
  C₁ : ℝ
  C₂ : ℝ
  nonnegative : 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂
  estimates : ∀ F : RicciFlow n M (Set.Icc t₀ t₁),
    CurveEvolutionAmbientBounds F P.K₀ P.K₁ P.K₂ →
      ∀ S : CurveEvolutionSolution F, CurveEvolutionEstimates S C₀ C₁ C₂

end PoincareConjecture
