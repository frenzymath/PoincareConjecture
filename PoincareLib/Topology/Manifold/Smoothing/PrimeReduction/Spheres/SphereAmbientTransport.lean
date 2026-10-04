import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexFrontierSubcomplex
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Polyhedra.Mathlib.PolyhedralPLChartHomeomorph
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Transport the whole original sphere through an actual PL homeomorphism

The source stays the complete cube sphere and the parametrization is the
literal composition with the same ambient map. See Prime029, section2.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- The same ambient PL homeomorphism transports the original sphere
and its complete chartwise PL map. See Prime029, section2. -/
theorem ChartwisePLSphere.nonempty_image
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (G : X ≃ₜ X)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (hG : ∀ i j, (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) :
    Nonempty (ChartwisePLSphere e (G '' S)) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨B, hB, hBs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  let K := B.frontierSubcomplex (closedBall (0 : V3) 1)
  have hK : K.faces.Finite := B.frontierSubcomplex_finite _ hB
  have hKs : K.space = sphere (0 : V3) 1 := by
    rw [B.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hBs,
      frontier_closedBall _ one_ne_zero]
  have hf : PolyhedralPLInCharts e s.map K.space := hKs.symm ▸ s.piecewiseAffine
  refine ⟨{
    parametrization := s.parametrization.trans (G.image S)
    map := G ∘ s.map
    map_eq := ?_
    piecewiseAffine := ?_ }⟩
  · intro x
    change G (s.map x) = G (s.parametrization x)
    rw [s.map_eq x]
  · simpa only [hKs] using hf.comp_chart_homeomorph K hK G hcover hG

end PoincareMT.M76
