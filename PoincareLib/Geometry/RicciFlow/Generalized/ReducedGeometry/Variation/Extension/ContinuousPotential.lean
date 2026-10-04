import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Extension.PotentialCoefficient

/-!
# Continuous scalar potential for a continuous gauge clock

The compact action bounds in Morgan-Tian Proposition 6.30,
pp. 118-119, require only continuity of the time lift. The actual
scalar curvature and cylinder map supply continuity of the spatial
potential throughout the admissible gauge coordinate domain.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- The actual gauge potential is continuous whenever its time lift
is continuous, the compact coefficient bound in Proposition 6.30,
pp. 118-119. No derivative of the clock is needed. -/
theorem backwardPotentialCoefficient_continuousOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (b : G.gaugeCover.index)
    (θ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x : G.gaugeCover.spatial b) {J : Set ℝ} (hθ : ContinuousOn θ J) :
    ContinuousOn (backwardPotentialCoefficient b θ x)
      (J ×ˢ (G.gaugeCover.spatial b : Set (EuclideanSpace ℝ (Fin n)))) := by
  have hc : ContinuousOn (chartAt (EuclideanSpace ℝ (Fin n)) x).symm
      (G.gaugeCover.spatial b : Set _) := by
    simpa only [(G.gaugeCover.spatial b).chartAt_target_eq] using
      (contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x)).continuousOn
  have hpair : ContinuousOn
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (θ z.1, (chartAt (EuclideanSpace ℝ (Fin n)) x).symm z.2))
      (J ×ˢ (G.gaugeCover.spatial b : Set _)) :=
    (hθ.comp continuousOn_fst (fun _ hz => hz.1)).prodMk
      (hc.comp continuousOn_snd (fun _ hz => hz.2))
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hscalar : Continuous (horizontalScalarCurvature G.leafwise) := H.scalar_smooth.continuous
  exact (Real.continuous_sqrt.comp continuous_fst).continuousOn.mul
    (hscalar.comp_continuousOn
      ((G.gaugeCover.cylinder b).smooth.continuous.comp_continuousOn hpair))

end PoincareMT.M14
