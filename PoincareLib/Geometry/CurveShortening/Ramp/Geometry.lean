import PoincareLib.Geometry.Riemannian.LoopSpace.Length.Basic
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import PoincareLib.Geometry.Riemannian.LoopSpace.Width

/-!
# Spatial product geometry for ramps

A ramp in `M × (ℝ / circumference ℤ)` is represented by its lift to `M × ℝ`.
The lifted last coordinate is circle arc length, never Ricci-flow time.
Covariant differentiation uses differentiated coordinates in the tangent
bundle and the chosen spatial connection. This works even where the
projection to `M` stops or intersects itself.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
variable {t₀ t₁ : ℝ}


/-- The tangent space of a spatial product with a circle, written in its lift. -/
abbrev RampTangent (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) :=
  TangentSpace (𝓡 n) p × ℝ

/-- The compact ambient Ricci flow used in Chapter 19. Its geometry is fixed
before any circumference or initial ramp is selected. -/
structure RampAmbientData where
  flow : RicciFlow n M (Set.Icc t₀ t₁)
  time_ordered : t₀ < t₁
  compact : IsCompact (Set.univ : Set M)
  hausdorff : T2Space M
  second_countable : SecondCountableTopology M
  curvature_bound : ℝ
  curvature_bound_nonnegative : 0 ≤ curvature_bound
  curvature_bounded : ∀ t ∈ Set.Icc t₀ t₁, ∀ p : M,
    (flow.connection t).curvatureTensorNorm p ≤ curvature_bound

/-- The exact product metric `g(t) ⊕ da²` on the circle cover. -/
noncomputable def rampMetricInner
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (t : ℝ) (p : M) (v w : RampTangent n M p) : ℝ :=
  (A.flow.metric t).inner p v.1 w.1 + v.2 * w.2

/-- The curvature of the spatial product has only horizontal components. -/
noncomputable def rampProductCurvature
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (t : ℝ) (p : M) (v : Fin 4 → RampTangent n M p) : ℝ :=
  (A.flow.connection t).curvatureTensor p (v 0).1 (v 1).1 (v 2).1 (v 3).1

noncomputable def rampVelocity
    (curve : ℝ → ℝ → M × ℝ) (x t : ℝ) : RampTangent n M (curve x t).1 :=
  (curveVelocity (n := n) (fun y ↦ (curve y t).1) x,
    deriv (fun y ↦ (curve y t).2) x)

noncomputable def rampTimeVelocity
    (curve : ℝ → ℝ → M × ℝ) (x t : ℝ) : RampTangent n M (curve x t).1 :=
  (curveVelocity (n := n) (fun s ↦ (curve x s).1) t,
    deriv (fun s ↦ (curve x s).2) t)

noncomputable def rampSpeed
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (x t : ℝ) : ℝ :=
  Real.sqrt (rampMetricInner A t (curve x t).1
    (rampVelocity curve x t) (rampVelocity curve x t))

noncomputable def rampUnitTangent
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (x t : ℝ) : RampTangent n M (curve x t).1 :=
  (rampSpeed A curve x t)⁻¹ • rampVelocity curve x t

/-- The pairing of the unit tangent with the positive unit circle direction. -/
noncomputable def rampCircleComponent
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (x t : ℝ) : ℝ :=
  (rampUnitTangent A curve x t).2

/-- Pullback covariant differentiation in a parameter direction. In the fixed
local tangent frame, this is the derivative of the vector's coefficients plus
the connection applied to its constant-coefficient local extension. -/
noncomputable def rampHorizontalCovariantDerivative
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (curve : ℝ → M) (Y : ∀ x, TangentSpace (𝓡 n) (curve x))
    (x : ℝ) : TangentSpace (𝓡 n) (curve x) :=
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) (curve x)
  e.symmL ℝ (curve x)
      (deriv (fun y ↦ (e ⟨curve y, Y y⟩).2) x) +
    D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y x))
      (curve x) (curveVelocity (n := n) curve x)

/-- `∇_S Y` in the spatial product. Both components differentiate `Y`, and
the circle component is the ordinary arc-length derivative. -/
noncomputable def rampCovariantDerivativeAt
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (t : ℝ)
    (Y : ∀ x, RampTangent n M (curve x t).1) (x : ℝ) :
    RampTangent n M (curve x t).1 :=
  ((rampSpeed A curve x t)⁻¹ •
      rampHorizontalCovariantDerivative (A.flow.connection t)
        (fun y ↦ (curve y t).1) (fun y ↦ (Y y).1) x,
    (rampSpeed A curve x t)⁻¹ * deriv (fun y ↦ (Y y).2) x)

/-- The genuine curvature vector `H = ∇_S S` of the lifted ramp. -/
noncomputable def rampCovariantAccelerationAt
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (t x : ℝ) : RampTangent n M (curve x t).1 :=
  rampCovariantDerivativeAt A curve t (fun y ↦ rampUnitTangent A curve y t) x

noncomputable def rampCurvatureSquaredAt
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (t x : ℝ) : ℝ :=
  rampMetricInner A t (curve x t).1
    (rampCovariantAccelerationAt A curve t x) (rampCovariantAccelerationAt A curve t x)

noncomputable def rampCurvatureAt
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (t x : ℝ) : ℝ :=
  Real.sqrt (rampCurvatureSquaredAt A curve t x)

/-- An actual recursive definition of `∇_S^i H`; order zero is `H`. -/
noncomputable def rampSpatialDerivative
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) : (i : ℕ) → (t x : ℝ) → RampTangent n M (curve x t).1
  | 0, t, x => rampCovariantAccelerationAt A curve t x
  | i + 1, t, x => rampCovariantDerivativeAt A curve t
      (fun y ↦ rampSpatialDerivative A curve i t y) x

noncomputable def rampDerivativeNormSquared
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (i : ℕ) (t x : ℝ) : ℝ :=
  rampMetricInner A t (curve x t).1
    (rampSpatialDerivative A curve i t x) (rampSpatialDerivative A curve i t x)

/-- A C² initial ramp with a degree-one arc-length lift. -/
structure RampInitialCurve
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (circumference : ℝ) where
  curve : ℝ → M × ℝ
  circumference_positive : 0 < circumference
  parameter_period : ∀ x, (curve (x + rampPeriod)).1 = (curve x).1
  degree_one_lift : ∀ x, (curve (x + rampPeriod)).2 = (curve x).2 + circumference
  spatial_regular : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 2 (fun x ↦ (curve x).1)
  circle_regular : ContDiff ℝ 2 (fun x ↦ (curve x).2)
  positive_circle_component : ∀ x,
    0 < rampCircleComponent A (fun y _ ↦ curve y) x t₀

/-- A classical solution with C2 spatial slices and joint C1 regularity in the
time interior. Fixed C2 parameter labels need not become smooth. Continuity
of the actual curve, velocity and curvature retains the endpoint data.
See Morgan--Tian p. 437 and the M63 legacy regularity review. -/
structure RampFlowSolution
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (circumference : ℝ) (initial : RampInitialCurve A circumference) where
  curve : ℝ → ℝ → M × ℝ
  continuous : ContinuousOn (fun p : ℝ × ℝ ↦ curve p.1 p.2)
    (Set.univ ×ˢ Set.Icc t₀ t₁)
  spatial_regular : ∀ t ∈ Set.Icc t₀ t₁,
    ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 2 (fun x ↦ (curve x t).1)
  circle_regular : ∀ t ∈ Set.Icc t₀ t₁,
    ContDiff ℝ 2 (fun x ↦ (curve x t).2)
  joint_c1_spatial_positive_time :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) 1
      (fun p : ℝ × ℝ ↦ (curve p.1 p.2).1) (Set.univ ×ˢ Set.Ioo t₀ t₁)
  joint_c1_circle_positive_time : ContDiffOn ℝ 1
    (fun p : ℝ × ℝ ↦ (curve p.1 p.2).2) (Set.univ ×ˢ Set.Ioo t₀ t₁)
  velocity_continuous : ContinuousOn
    (fun p : ℝ × ℝ ↦ ((⟨(curve p.1 p.2).1, (rampVelocity (n := n) curve p.1 p.2).1⟩ :
      TangentBundle (𝓡 n) M), (rampVelocity (n := n) curve p.1 p.2).2))
    (Set.univ ×ˢ Set.Icc t₀ t₁)
  curvature_continuous : ContinuousOn
    (fun p : ℝ × ℝ ↦ ((⟨(curve p.1 p.2).1,
      (rampCovariantAccelerationAt A curve p.2 p.1).1⟩ : TangentBundle (𝓡 n) M),
      (rampCovariantAccelerationAt A curve p.2 p.1).2))
    (Set.univ ×ˢ Set.Icc t₀ t₁)
  parameter_period : ∀ x t, (curve (x + rampPeriod) t).1 = (curve x t).1
  degree_one_lift : ∀ x t,
    (curve (x + rampPeriod) t).2 = (curve x t).2 + circumference
  initial_eq : ∀ x, curve x t₀ = initial.curve x
  positive_circle_component : ∀ t ∈ Set.Icc t₀ t₁, ∀ x,
    0 < rampCircleComponent A curve x t
  shrinking_equation : ∀ t ∈ Set.Ioo t₀ t₁, ∀ x,
    rampTimeVelocity curve x t = rampCovariantAccelerationAt A curve t x

noncomputable def rampArcLength
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (t a b : ℝ) : ℝ :=
  ∫ x in a..b, rampSpeed A curve x t

noncomputable def rampArcTotalCurvature
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (t a b : ℝ) : ℝ :=
  ∫ x in a..b, rampCurvatureAt A curve t x * rampSpeed A curve x t

noncomputable def rampTotalLength
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (t : ℝ) : ℝ :=
  rampArcLength A curve t 0 rampPeriod

noncomputable def rampTotalCurvature
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    (curve : ℝ → ℝ → M × ℝ) (t : ℝ) : ℝ :=
  rampArcTotalCurvature A curve t 0 rampPeriod

noncomputable def initialRampLength
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    {circumference : ℝ} (I : RampInitialCurve A circumference) : ℝ :=
  rampTotalLength A (fun x _ ↦ I.curve x) t₀

noncomputable def initialRampTotalCurvature
    (A : RampAmbientData (n := n) (M := M) (t₀ := t₀) (t₁ := t₁))
    {circumference : ℝ} (I : RampInitialCurve A circumference) : ℝ :=
  rampTotalCurvature A (fun x _ ↦ I.curve x) t₀

end PoincareMT

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- C² regularity in the fixed standard angular parameter on the circle. -/
def IsC2FreeLoop (loop : C1FreeLoopSpace (M := M)) : Prop :=
  ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) 2 (periodicFreeLoop loop)

/-- The degree-one graph lift from Lemma 19.17, at constant circle speed. -/
noncomputable def canonicalRampLift (loop : C1FreeLoopSpace (M := M))
    (circumference x : ℝ) : M × ℝ :=
  (periodicFreeLoop loop x, circumference * x / rampPeriod)

end PoincareMT
