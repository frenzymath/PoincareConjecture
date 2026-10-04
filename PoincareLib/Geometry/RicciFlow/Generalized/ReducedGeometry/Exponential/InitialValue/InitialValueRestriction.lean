import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.PathRestriction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Pullback.PullbackRestriction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential

/-!
# Restricting actual square-root initial-value paths

Morgan-Tian Definition 6.17 and Lemma 6.18, pp. 113-114.
A positive prefix retains the actual square curve, velocity and
extension. Unique within differentiation preserves its closed Euler
equations and its initial velocity, giving downward closure of survival.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ σ : ℝ} {x y : G.Point} {Z : G.Horizontal x}

/-- Restrict a frozen square-root initial-value path to a positive
earlier final time, preserving its actual square curve, velocity and
extension. This is the prefix property of Definition 6.17, p. 113. -/
def initialValuePathRestrict (P : M14SquareRootInitialValuePath G T τ x y Z)
    (hσ : 0 < σ) (hστ : σ ≤ τ) :
    M14SquareRootInitialValuePath G T σ x (P.path.curve σ) Z := by
  let q : M14BackwardPath G T 0 σ x (P.path.curve σ) :=
    { restrictPath P.path 0 σ le_rfl hσ hστ with
      base_time := P.path.base_time
      curve_start := P.path.curve_start }
  have hsub : M14SqrtParameterInterval 0 σ ⊆ M14SqrtParameterInterval 0 τ :=
    Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hστ)
  have hC : UniqueDiffOn ℝ (M14SqrtParameterInterval 0 σ) :=
    uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (le_refl (0 : ℝ)) hσ)
  have hR := P.square_path.smooth.mono P.square_path.interval_subset
  let R : M14SquareRootPath G q := {
    curve := P.square_path.curve
    domain := P.square_path.domain
    interval_subset := hsub.trans P.square_path.interval_subset
    smooth := P.square_path.smooth
    agrees := fun s hs => P.square_path.agrees s (hsub hs)
    curve_time := fun s hs => P.square_path.curve_time s (hsub hs)
    horizontal_velocity := P.square_path.horizontal_velocity
    horizontal_agrees := fun s hs => P.square_path.horizontal_agrees s
      ⟨hs.1, hs.2.trans_le (Real.sqrt_le_sqrt hστ)⟩
    derivative_eq := fun s hs => by
      rw [mfderivWithin_subset hsub (hC s hs).uniqueMDiffWithinAt
        ((hR s (hsub hs)).mdifferentiableWithinAt (by simp))]
      exact P.square_path.derivative_eq s (hsub hs) }
  refine {
    path := q
    square_path := R
    extension := pullbackExtensionRestrict P.extension hsub
    euler := ?_
    initial_velocity := P.initial_velocity }
  intro s hs W
  have hD := horizontalCovariantDerivative_restrict_subset P.extension hsub (hC s hs)
    ((hR s (hsub hs)).mdifferentiableWithinAt (by simp))
  unfold M14SquareRootEulerResidual M14SquareRootVelocity
  dsimp only [R]
  rw [← hD]
  exact P.euler s (hsub hs) W

/-- Positive survival of a frozen square-root initial-value problem
implies survival to every positive earlier time, Definition 6.17
and Lemma 6.18, pp. 113-114. -/
theorem exists_initialValuePath_prefix
    (P : M14SquareRootInitialValuePath G T τ x y Z) (hσ : 0 < σ) (hστ : σ ≤ τ) :
    ∃ z : G.Point, Nonempty (M14SquareRootInitialValuePath G T σ x z Z) :=
  ⟨P.path.curve σ, ⟨initialValuePathRestrict P hσ hστ⟩⟩

end PoincareMT.M14
