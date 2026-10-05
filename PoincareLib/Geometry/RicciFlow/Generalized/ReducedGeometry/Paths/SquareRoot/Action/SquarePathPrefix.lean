import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.PathPrefix
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Pullback.PullbackRestriction

/-!
# Square-root paths on a strict prefix

Morgan-Tian Definition 6.17 and Proposition 6.30, pp. 113, 118-119.
Restriction retains the square curve, horizontal velocity and Euler
equation, including the new closed endpoint by derivative uniqueness.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b c : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

/-- A square path restricts to any positive-length prefix, retaining its
actual curve and velocity, Definition 6.17 and Proposition 6.30, pp. 113, 118-119. -/
def prefixSquarePath (R : M14SquareRootPath G p) (hac : a < c) (hcb : c ≤ b) :
    M14SquareRootPath G (prefixPath p c hac hcb) := by
  have hsub : M14SqrtParameterInterval a c ⊆ M14SqrtParameterInterval a b :=
    Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hcb)
  have hC : UniqueDiffOn ℝ (M14SqrtParameterInterval a c) :=
    uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg hac)
  refine {
    curve := R.curve
    domain := R.domain
    interval_subset := hsub.trans R.interval_subset
    smooth := R.smooth
    agrees := fun s hs => R.agrees s (hsub hs)
    curve_time := fun s hs => R.curve_time s (hsub hs)
    horizontal_velocity := R.horizontal_velocity
    horizontal_agrees := fun s hs => R.horizontal_agrees s
      ⟨hs.1, hs.2.trans_le (Real.sqrt_le_sqrt hcb)⟩
    derivative_eq := ?_ }
  intro s hs
  rw [mfderivWithin_subset hsub (hC s hs).uniqueMDiffWithinAt
    ((R.smooth.mono R.interval_subset s (hsub hs)).mdifferentiableWithinAt (by simp))]
  exact R.derivative_eq s (hsub hs)

/-- The actual square Euler equation persists under closed prefix
restriction with the original extension, Proposition 6.30, pp. 118-119. -/
theorem prefixSquarePath_euler (R : M14SquareRootPath G p) (hac : a < c) (hcb : c ≤ b)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) R.horizontal_velocity)
    (hEuler : ∀ s ∈ M14SqrtParameterInterval a b, ∀ W,
      M14SquareRootEulerResidual G R E s W = 0) :
    ∀ s ∈ M14SqrtParameterInterval a c, ∀ W,
      M14SquareRootEulerResidual G (prefixSquarePath R hac hcb)
        (pullbackExtensionRestrict E (Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hcb))) s W = 0 := by
  intro s hs W
  have hsub : M14SqrtParameterInterval a c ⊆ M14SqrtParameterInterval a b :=
    Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hcb)
  have hD := horizontalCovariantDerivative_restrict_subset E hsub
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg hac) s hs)
    ((R.smooth.mono R.interval_subset s (hsub hs)).mdifferentiableWithinAt (by simp))
  unfold M14SquareRootEulerResidual M14SquareRootVelocity
  dsimp only [prefixSquarePath]
  rw [← hD]
  exact hEuler s (hsub hs) W

end PoincareMT.M14
