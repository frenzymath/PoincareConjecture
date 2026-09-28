import PoincareConjecture.Definitions.Ch06.LGeometry
import PoincareConjecture.Definitions.Ch01.TensorOperators
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic










set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
variable {t₀ t₁ : ℝ}
variable {F : RicciFlow n M (Set.Icc t₀ t₁)}


noncomputable def curvePeriod : ℝ := 2 * Real.pi


noncomputable def curveSpeed (F : RicciFlow n M (Set.Icc t₀ t₁))
    (curve : ℝ → ℝ → M) (t x : ℝ) : ℝ :=
  (F.metric t).tangentNorm (curve x t)
    (curveVelocity (n := n) (fun y ↦ curve y t) x)


noncomputable def spatialUnitTangent (F : RicciFlow n M (Set.Icc t₀ t₁))
    (curve : ℝ → ℝ → M) (t x : ℝ) : TangentSpace (𝓡 n) (curve x t) :=
  (curveSpeed F curve t x)⁻¹ •
    curveVelocity (n := n) (fun y ↦ curve y t) x

namespace CurveShrinkingFlow


structure Data (F : RicciFlow n M (Set.Icc t₀ t₁)) where
  curve : ℝ → ℝ → M
  time_nontrivial : t₀ < t₁
  regular : ∀ t : ℝ, ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 2
    (fun x ↦ curve x t) Set.univ
  time_regular : ∀ x : ℝ, ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 2
    (fun t ↦ curve x t) (Set.Icc t₀ t₁)
  joint_regular : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
    (fun z : ℝ × ℝ ↦ curve z.1 z.2) (Set.univ ×ˢ Set.Icc t₀ t₁)
  periodic : ∀ (x t : ℝ), curve (x + curvePeriod) t = curve x t
  immersed : ∀ (x t : ℝ),
    curveVelocity (n := n) (fun y ↦ curve y t) x ≠ 0
  spatial_unit_extension :
    ∀ (t : ℝ),
      SmoothAlongCurveExtensionOn Set.univ
        (fun x ↦ curve x t)
        (fun x ↦ spatialUnitTangent F (curve := curve) t x)

end CurveShrinkingFlow

open CurveShrinkingFlow


noncomputable def curveCurvatureVector
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t x : ℝ) :
    TangentSpace (𝓡 n) (P.curve x t) :=
  alongCovariantDerivative F (fun _ ↦ t) (fun y ↦ P.curve y t)
    (fun y ↦ spatialUnitTangent F P.curve t y) Set.univ (P.spatial_unit_extension t)
    (spatialUnitTangent F P.curve t) x (by simp)


def SatisfiesCurveShrinkingEquation
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) : Prop :=
  ∀ (x t : ℝ), t ∈ Set.Icc t₀ t₁ →
    curveVelocity (n := n) (fun s ↦ P.curve x s) t =
      curveCurvatureVector P t x


noncomputable def curveCurvatureSquared
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t x : ℝ) : ℝ :=
  (F.metric t).inner (P.curve x t) (curveCurvatureVector P t x)
    (curveCurvatureVector P t x)


noncomputable def curveCurvature
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t x : ℝ) : ℝ :=
  Real.sqrt (curveCurvatureSquared P t x)


noncomputable def normalCovariantDerivative
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t x : ℝ)
    (E : SmoothAlongCurveExtensionOn Set.univ
      (fun y ↦ P.curve y t)
      (fun y ↦ curveCurvatureVector P t y)) :
    TangentSpace (𝓡 n) (P.curve x t) :=
  let A := alongCovariantDerivative F (fun _ ↦ t) (fun y ↦ P.curve y t)
      (fun y ↦ curveCurvatureVector P t y) Set.univ E
      (spatialUnitTangent F P.curve t) x (by simp)
  A - (F.metric t).inner (P.curve x t) A (spatialUnitTangent F P.curve t x) •
    spatialUnitTangent F P.curve t x


noncomputable def arcLengthDerivative
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (curveSpeed F P.curve t x)⁻¹ * deriv f x


noncomputable def arcLengthSecondDerivativeOf
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F)
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  arcLengthDerivative P t
    (fun y ↦ arcLengthDerivative P t f y) x


noncomputable def arcLengthSecondDerivative
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t x : ℝ) : ℝ :=
  arcLengthDerivative P t
    (fun y ↦ arcLengthDerivative P t (fun z ↦ curveCurvatureSquared P t z) y) x


noncomputable def totalCurveLength
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..curvePeriod, curveSpeed F P.curve t x


noncomputable def totalCurveCurvature
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..curvePeriod,
    curveCurvature P t x * curveSpeed F P.curve t x

end PoincareConjecture
