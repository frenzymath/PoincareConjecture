import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Confinement.Coordinates.SpatialLift
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Confinement.Coordinates.LiftedVelocity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Basic

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Lemma8_7_SquareRootLift.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# The speed of an actual square-root path lift

Morgan-Tian Claims 8.6-8.7, pp. 173-174. The compatible-cylinder metric
identifies spatial speed with M14's horizontal speed on a closed prefix.
See `references/ricci-flow/mapher/noncollapse/derivations/2026-09-21-lifted-velocity.md`.
-/

set_option autoImplicit false
-- The actual tangent fibers retain their selected model instances.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareMT.Generalized.Noncollapse

/-- A supplied lift of the actual square-root path has exactly its
horizontal speed in the cylinder metric. This is the metric identification
for Claims 8.6-8.7, pp. 173-174, including both prefix endpoints. -/
theorem squareRootPath_lift_speed_eq
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I K : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport n X time I)
    (D : SmoothSpacetimeInterval K)
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder G.spacetime D C)
    (g : SpacetimeCylinderMetric e)
    {T tau : ℝ} {x y : G.Point} {p : M14BackwardPath G T 0 tau x y}
    (R : M14SquareRootPath G p)
    {S : ℝ} (hS : 0 < S) (hStau : S ≤ Real.sqrt tau)
    (L : ℝ → D.Point × C)
    (hL : ∀ s ∈ Set.Icc 0 S, e.toSpacetime (L s) = R.curve s)
    (s : ℝ) (hs : s ∈ Set.Icc 0 S) :
    (g.metric (L s).1.val).tangentNorm (L s).2
      (mfderivWithin 𝓘(ℝ) (𝓡 n) (fun r => (L r).2) (Set.Icc 0 S) s 1) =
      Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s)) := by
  have hsub : Icc 0 S ⊆ M14SqrtParameterInterval 0 tau := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using
      (show Icc 0 S ⊆ Icc 0 (Real.sqrt tau) from fun _ ht =>
        ⟨ht.1, ht.2.trans hStau⟩)
  have hR := R.smooth.mono R.interval_subset
  have hLs := compatibleCylinder_lift_contMDiffOn G D e g (hR.mono hsub) L hL
  have hU := uniqueDiffOn_Icc hS s hs
  have hproj := compatibleCylinder_horizontalDerivative_lift e g L
    ((hLs s hs).mdifferentiableWithinAt (by simp)) hU
  have hderiv :
      mfderivWithin 𝓘(ℝ) (spacetimeModel n) (e.toSpacetime ∘ L) (Icc 0 S) s 1 =
        -(2 * s) • G.spacetime.timeVector (R.curve s) +
          (R.horizontal_velocity s).val := by
    have hsame := congrArg (fun A : ℝ →L[ℝ] SpacetimeModelVector n => A 1)
      (mfderivWithin_congr (I := 𝓘(ℝ)) (I' := spacetimeModel n) hL (hL s hs))
    have hrestrict := congrArg (fun A : ℝ →L[ℝ] SpacetimeModelVector n => A 1)
      (((hR s (hsub hs)).mdifferentiableWithinAt (by simp)).mfderivWithin_mono
        hU.uniqueMDiffWithinAt hsub)
    exact hsame.trans (hrestrict.trans (R.derivative_eq s (hsub hs)))
  have htime : G.spacetime.horizontalProjection (R.curve s)
      (G.spacetime.timeVector (R.curve s)) = 0 := by
    apply Subtype.ext
    simp only [G.spacetime.horizontalProjection_eq,
      G.spacetime.timeVector_normalized, one_smul, sub_self]
    rfl
  unfold RiemannianMetric.tangentNorm
  rw [g.metric_eq, hproj]
  change Real.sqrt (G.spacetime.horizontalMetric.inner (e.toSpacetime (L s))
    (G.spacetime.horizontalProjection (e.toSpacetime (L s))
      (mfderivWithin 𝓘(ℝ) (spacetimeModel n) (e.toSpacetime ∘ L) (Icc 0 S) s 1))
    (G.spacetime.horizontalProjection (e.toSpacetime (L s))
      (mfderivWithin 𝓘(ℝ) (spacetimeModel n) (e.toSpacetime ∘ L) (Icc 0 S) s 1))) = _
  rw [hL s hs, hderiv, map_add, map_smul, htime, smul_zero,
    G.spacetime.horizontalProjection_identity, zero_add]

end PoincareMT.Generalized.Noncollapse
