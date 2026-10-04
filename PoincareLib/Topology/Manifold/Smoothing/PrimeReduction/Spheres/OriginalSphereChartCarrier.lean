import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Coordinates.FiniteChartSurfaceImage
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexFrontierSubcomplex
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Simplicial.Mathlib.EmptyInteriorFaceDimension

/-!
# Construct the chart carrier of the whole original PL sphere

The finite cube-frontier source and its empty interior give the source
face bound. Exact chart images then supply the whole original carrier
and its inverse-chart membership test. See PrimeReduction028.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- An actual chartwise PL sphere constructs its complete finite chart
image inside a retained coordinate window. Neither a finite source
model nor a surface dimension bound is a supplier. See Prime028. -/
theorem ChartwisePLSphere.exists_finite_chart_carrier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) :
    ∃ P : SimplicialComplex ℝ V3, P.faces.Finite ∧
      P.space = Q '' (S ∩ Q.source) ∩ J.space ∧
      (∀ a ∈ P.faces, a.card ≤ 3) ∧
      ∀ x ∈ J.space, Q.symm x ∈ S ↔ x ∈ P.space := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨B, hB, hBs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  let K := B.frontierSubcomplex (closedBall (0 : V3) 1)
  have hK : K.faces.Finite := B.frontierSubcomplex_finite _ hB
  have hKs : K.space = sphere (0 : V3) 1 := by
    rw [B.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hBs,
      frontier_closedBall _ one_ne_zero]
  have hint : interior K.space = ∅ := by
    rw [hKs, interior_sphere _ one_ne_zero]
  have hcard (a : Finset V3) (ha : a ∈ K.faces) : a.card ≤ 2 + 1 := by
    simpa using K.face_card_le_of_interior_space_eq_empty hint ha
  have hmap : s.map '' sphere (0 : V3) 1 = S := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [s.map_eq ⟨x, hx⟩]
      exact (s.parametrization ⟨x, hx⟩).property
    · intro x hx
      obtain ⟨z, hz⟩ := s.parametrization.surjective ⟨x, hx⟩
      refine ⟨z, z.property, ?_⟩
      rw [s.map_eq z, hz]
  have hf : PolyhedralPLInCharts e s.map K.space := hKs.symm ▸ s.piecewiseAffine
  obtain ⟨P, hP, hPs, hPc⟩ :=
    hf.exists_finite_chart_image_of_face_card_le K hK hcard Q hQ J hJ hJQ
  have hwhole : P.space = Q '' (S ∩ Q.source) ∩ J.space := by
    simpa only [hKs, hmap] using hPs
  refine ⟨P, hP, hwhole, hPc, ?_⟩
  intro x hx
  constructor
  · intro hxS
    exact hwhole.symm.subset
      ⟨⟨Q.symm x, ⟨hxS, Q.map_target (hJQ hx)⟩, Q.right_inv (hJQ hx)⟩, hx⟩
  · intro hxP
    obtain ⟨⟨y, ⟨hyS, hyQ⟩, rfl⟩, _⟩ := hwhole.subset hxP
    simpa only [Q.left_inv hyQ] using hyS


/-- Every point of a chartwise PL sphere belongs to its given atlas. -/
theorem ChartwisePLSphere.chart_source_cover
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) : ∀ y ∈ S, ∃ i, y ∈ (e i).source := by
  intro y hy
  obtain ⟨v, hv⟩ := s.parametrization.surjective ⟨y, hy⟩
  obtain ⟨i, P, V, _, _, _, hvV, hVP, hPe, _⟩ := s.piecewiseAffine.coordinates v
  refine ⟨i, ?_⟩
  have hsource := hPe (hVP (mem_image_of_mem Subtype.val hvV))
  simpa only [s.map_eq v, hv] using hsource

end PoincareMT.M76
