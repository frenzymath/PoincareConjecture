import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugeCovariantFields
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugeVelocity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Pullback.PullbackRestriction
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Pullback.PullbackCongruence

/-!
# Actual base fields in a relative compatible gauge

Morgan-Tian Lemma 6.8 and Proposition 6.33, pp. 108-109, 120-121.
The supplied square-root velocity and every actual field derivative
are identified with their within coordinate expressions on a relative
gauge neighborhood. This includes the base acceleration in the Euler
term of the surface second-variation formula.
-/

set_option autoImplicit false
-- Within tangent coordinates and equal horizontal base fibers retain their fixed models.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p) (b : G.gaugeCover.index)
  {N : Set ℝ}
  {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b}

/-- The supplied square-root velocity is exactly the spatial within
coordinate derivative in any relative gauge, Lemma 6.8, pp. 108-109. -/
theorem squareRootVelocity_gauge (hN : IsOpen N)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β
      (M14SqrtParameterInterval τ₁ τ₂ ∩ N))
    (hrec : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N,
      (G.gaugeCover.cylinder b).toSpacetime (β r) = R.curve r)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N) :
    HEq (R.horizontal_velocity s)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
        (derivWithin (fun r => (β r).2.val) (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s)) := by
  have hS := (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)).inter hN
  have hp := gaugeCurve_projectedVelocityWithin b
    ((hβ s hs).mdifferentiableWithinAt (by simp)) (hS s hs)
  have hc := projectedCurveVelocityWithin_congrOn (G := G)
    (fun r hr => (hrec r hr).symm) hs
  have hleft : projectedCurveVelocityWithin G R.curve
      (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s = R.horizontal_velocity s := by
    unfold projectedCurveVelocityWithin
    rw [mfderivWithin_inter (hN.mem_nhds hs.2)]
    exact (squareRoot_horizontalVelocity_eq_projection R hs.1).symm
  rw [hleft] at hc
  exact hc.trans (heq_of_eq hp)

/-- An arbitrary actual base field has its within coordinate
covariant derivative in a relative gauge, for every supplied extension,
Proposition 6.33, pp. 120-121. -/
theorem baseCovariantDerivative_gauge
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (x₀ : G.gaugeCover.spatial b) (hN : IsOpen N)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β
      (M14SqrtParameterInterval τ₁ τ₂ ∩ N))
    (hrec : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N,
      (G.gaugeCover.cylinder b).toSpacetime (β r) = R.curve r)
    (hclock : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, (β r).1.val = T - r ^ 2)
    {Y : ∀ r, G.Horizontal (R.curve r)}
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y)
    (f : ℝ → EuclideanSpace ℝ (Fin n))
    (hY : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N,
      HEq (Y r) ((G.gaugeCover.metric b).spatialTangentEquiv (β r).1 (β r).2 (f r)))
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N) :
    HEq (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y E s)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
        (derivWithin f (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s +
          M08.closedChartConnection W.flow T x₀ (M14SqrtParameterInterval τ₁ τ₂ ∩ N)
            (s, (β s).2.val)
            (derivWithin (fun r => (β r).2.val) (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s)
            (f s))) := by
  let S := M14SqrtParameterInterval τ₁ τ₂ ∩ N
  let γ := fun r => (G.gaugeCover.cylinder b).toSpacetime (β r)
  let Y' : ∀ r, G.Horizontal (γ r) := fun r =>
    (G.gaugeCover.metric b).spatialTangentEquiv (β r).1 (β r).2 (f r)
  let E₀ := pullbackExtensionRestrict E (K := S) inter_subset_left
  have hγ : EqOn R.curve γ S := fun r hr => (hrec r hr).symm
  let E' := pullbackExtensionCongrOn E₀ hγ hY
  have hS := (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)).inter hN
  have hc := horizontalCovariantDerivative_gauge_chart b hCoordinates W T x₀ hclock E' hs
    (hS s hs) ((hβ s hs).mdifferentiableWithinAt (by simp))
  have hform : M14HorizontalCovariantDerivative G γ S Y' E' s =
      (G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
        (derivWithin f S s + M08.closedChartConnection W.flow T x₀ S (s, (β s).2.val)
          (derivWithin (fun r => (β r).2.val) S s) (f s)) := by
    apply ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2).symm.injective
    simpa only [Y', ContinuousLinearEquiv.symm_apply_apply] using hc
  exact (heq_of_eq (horizontalCovariantDerivative_restrict_inter E
    (hN.mem_nhds hs.2))).trans
      ((horizontalCovariantDerivative_congrOn E₀ hγ hY hs).trans (heq_of_eq hform))

/-- The actual base acceleration is the second within coordinate
derivative plus the quadratic connection term, for every supplied
velocity extension, Proposition 6.33, pp. 120-121. -/
theorem squareRootCovariantVelocity_gauge
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (x₀ : G.gaugeCover.spatial b) (hN : IsOpen N)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β
      (M14SqrtParameterInterval τ₁ τ₂ ∩ N))
    (hrec : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N,
      (G.gaugeCover.cylinder b).toSpacetime (β r) = R.curve r)
    (hclock : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, (β r).1.val = T - r ^ 2)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N) :
    HEq (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂)
        R.horizontal_velocity E s)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
        (derivWithin (derivWithin (fun r => (β r).2.val)
            (M14SqrtParameterInterval τ₁ τ₂ ∩ N)) (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s +
          M08.closedChartConnection W.flow T x₀ (M14SqrtParameterInterval τ₁ τ₂ ∩ N)
            (s, (β s).2.val)
            (derivWithin (fun r => (β r).2.val) (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s)
            (derivWithin (fun r => (β r).2.val) (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s))) :=
  baseCovariantDerivative_gauge R b hCoordinates W x₀ hN hβ hrec hclock E _
    (fun _ hr => squareRootVelocity_gauge R b hN hβ hrec hr) hs

end PoincareMT.M14
