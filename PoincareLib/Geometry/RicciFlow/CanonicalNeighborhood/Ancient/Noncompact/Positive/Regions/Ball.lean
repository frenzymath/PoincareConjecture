import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Euclidean
import PoincareLib.Topology.Manifold.Schoenflies.Neighborhood
import PoincareLib.Topology.Manifold.Schoenflies.BallImages

/-!
# Smooth ball neighborhoods of the compact soul side

Apply the existing smooth Schoenflies neighborhood theorem to the actual
Euclidean image of the compact side, then transport back to the solution.
This uses the independently tracked Schoenflies filling admission. It does
not assume a cap certificate or construct compatible epsilon-neck collars.

Reference: Morgan--Tian, Corollary 9.88, pp. 239--240, positive-curvature case;
Hatcher, Notes on Basic 3-Manifold Topology, Section 1.1, Theorem 1.1, pp. 1--5.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.NoncompactKappa.Positive.SoulNeckRegion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {epsilon D R : ℝ}
  (G : SoulNeckRegion K S epsilon D R)

/-- The compact side is exactly a smooth closed ball, with a parametrization
defined on a neighborhood of the ball and preserving its boundary sphere. -/
theorem exists_closed_side_ball_neighborhood :
    ∃ b : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M,
      Metric.closedBall 0 1 ⊆ b.source ∧
      closure G.inside ⊆ b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 = closure G.inside ∧
      b '' Metric.ball 0 1 = G.inside ∧
      b '' Metric.sphere 0 1 = G.neck.terminal_neck.central_sphere := by
  obtain ⟨Omega⟩ := G.nonempty_smoothDomain_euclidean_inside
  obtain ⟨b, hbs, hbt, hb, hbi, hbimage⟩ := Omega.exists_ball_neighborhood
    (fun p : UnitTwoSphere =>
      S.euclidean.symm (G.neck.terminal_neck.coordinate_map (p, 0)))
    G.euclidean_boundary_isSmoothEmbedding G.range_euclidean_boundary
  let e := S.euclidean.toHomeomorph.toOpenPartialHomeomorph
  let c := b.trans e
  have hcs : Metric.closedBall 0 1 ⊆ c.source := fun x hx => ⟨hbs hx, mem_univ _⟩
  have hci : c '' Metric.closedBall 0 1 = closure G.inside := by
    change (S.euclidean ∘ b) '' Metric.closedBall 0 1 = closure G.inside
    simp only [Function.comp_def]
    rw [← Set.image_image (⇑S.euclidean) (⇑b), hbimage,
      G.closure_euclidean_inside, Set.image_image]
    simp only [S.euclidean.apply_symm_apply, image_id']
  refine ⟨c, hcs, ?_, ?_, ?_, hci, ?_, ?_⟩
  · intro x hx
    refine ⟨mem_univ _, ?_⟩
    apply hbt
    rw [G.closure_euclidean_inside]
    exact mem_image_of_mem _ hx
  · exact S.euclidean.contMDiff.comp_contMDiffOn (hb.mono (fun x hx => hx.1))
  · exact hbi.comp S.euclidean.symm.contMDiff.contMDiffOn (fun x hx => hx.2)
  · rw [c.image_ball_eq_interior hcs hci, G.interior_closure_inside]
  · rw [c.image_sphere_eq_frontier hcs hci, G.frontier_closure_inside]

end PoincareMT.NoncompactKappa.Positive.SoulNeckRegion
