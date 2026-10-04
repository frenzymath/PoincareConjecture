import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import PoincareLib.Geometry.Riemannian.Tensor.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Curve shortening in an ambient Ricci flow

The real parameter interval below is a periodic representative of `S¹`.
All vector derivatives below use the actual spatial Levi-Civita connection.
The milestone retains the corrected upper bounds; constructing the auxiliary
spacetime curvature used in their source proof is not part of these definitions.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
variable {t₀ t₁ : ℝ}
variable {F : RicciFlow n M (Set.Icc t₀ t₁)}

/-- The period of the real representative of the parameter circle. -/
noncomputable def curvePeriod : ℝ := 2 * Real.pi

/-- Speed of a periodic curve at a fixed time. -/
noncomputable def curveSpeed (F : RicciFlow n M (Set.Icc t₀ t₁))
    (curve : ℝ → ℝ → M) (t x : ℝ) : ℝ :=
  (F.metric t).tangentNorm (curve x t)
    (curveVelocity (n := n) (fun y ↦ curve y t) x)

/-- Unit tangent in the increasing parameter direction. -/
noncomputable def spatialUnitTangent (F : RicciFlow n M (Set.Icc t₀ t₁))
    (curve : ℝ → ℝ → M) (t x : ℝ) : TangentSpace (𝓡 n) (curve x t) :=
  (curveSpeed F curve t x)⁻¹ •
    curveVelocity (n := n) (fun y ↦ curve y t) x

namespace CurveShrinkingFlow

/-- A smooth immersed periodic family in the ambient Ricci flow. -/
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

/-- Curvature vector `H = ∇_S S`, using the supplied local unit-tangent extension. -/
noncomputable def curveCurvatureVector
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t x : ℝ) :
    TangentSpace (𝓡 n) (P.curve x t) :=
  alongCovariantDerivative F (fun _ ↦ t) (fun y ↦ P.curve y t)
    (fun y ↦ spatialUnitTangent F P.curve t y) Set.univ (P.spatial_unit_extension t)
    (spatialUnitTangent F P.curve t) x (by simp)

/-- The curve-shrinking equation `∂ₜc = H`. -/
def SatisfiesCurveShrinkingEquation
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) : Prop :=
  ∀ (x t : ℝ), t ∈ Set.Icc t₀ t₁ →
    curveVelocity (n := n) (fun s ↦ P.curve x s) t =
      curveCurvatureVector P t x

/-- Squared curvature `k² = ⟨H,H⟩`. -/
noncomputable def curveCurvatureSquared
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t x : ℝ) : ℝ :=
  (F.metric t).inner (P.curve x t) (curveCurvatureVector P t x)
    (curveCurvatureVector P t x)

/-- Curvature `k = |H|`, totalized by the nonnegative square root. -/
noncomputable def curveCurvature
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t x : ℝ) : ℝ :=
  Real.sqrt (curveCurvatureSquared P t x)

/-- The normal component of `∇_S H`. -/
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

/-- First derivative with respect to arc length at a fixed time. -/
noncomputable def arcLengthDerivative
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (curveSpeed F P.curve t x)⁻¹ * deriv f x

/-- Second arc-length derivative, obtained by iterating the preceding operator. -/
noncomputable def arcLengthSecondDerivativeOf
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F)
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  arcLengthDerivative P t
    (fun y ↦ arcLengthDerivative P t f y) x

/-- Second arc-length derivative of the squared curvature. -/
noncomputable def arcLengthSecondDerivative
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t x : ℝ) : ℝ :=
  arcLengthDerivative P t
    (fun y ↦ arcLengthDerivative P t (fun z ↦ curveCurvatureSquared P t z) y) x

/-- Total length of a periodic curve. -/
noncomputable def totalCurveLength
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..curvePeriod, curveSpeed F P.curve t x

/-- Total curvature of a periodic curve. -/
noncomputable def totalCurveCurvature
    (P : CurveShrinkingFlow.Data (n := n) (M := M) F) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..curvePeriod,
    curveCurvature P t x * curveSpeed F P.curve t x

end PoincareMT
