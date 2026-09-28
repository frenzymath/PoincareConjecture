import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X G ι : Type*} [TopologicalSpace X]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]




theorem ChartwisePLBall.exists_finite_graph_images
    {e : ι → OpenPartialHomeomorph X V3} {D S : Set X}
    (b : ChartwisePLBall e D S) (F : X → G)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) :
    ∃ P Q : SimplicialComplex ℝ G,
      P.faces.Finite ∧ Q.faces.Finite ∧ P.space = F '' D ∧ Q.space = F '' S := by
  have hmapD : b.map '' closedBall (0 : V3) 1 = D := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [b.map_eq ⟨x, hx⟩]
      exact (b.parametrization ⟨x, hx⟩).property
    · intro x hx
      obtain ⟨z, hz⟩ := b.parametrization.surjective ⟨x, hx⟩
      refine ⟨z, z.property, ?_⟩
      rw [b.map_eq z, hz]
  have hmapS : b.map '' sphere (0 : V3) 1 = S := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      let z : closedBall (0 : V3) 1 := ⟨x, sphere_subset_closedBall hx⟩
      rw [b.map_eq z]
      exact (b.boundary_eq z).mpr hx
    · intro x hx
      obtain ⟨z, hz⟩ := b.parametrization.surjective ⟨x, b.boundary_subset hx⟩
      have hzS : (b.parametrization z : X) ∈ S := by rw [hz]; exact hx
      refine ⟨z, (b.boundary_eq z).mp hzS, ?_⟩
      rw [b.map_eq z, hz]
  obtain ⟨_, C, _, _, _, c, hc, _⟩ := isFinitePLBallPair_unit_cube (ι := Fin 3)
  obtain ⟨f, ⟨K, hK, hKD, _⟩, _⟩ := hc
  let J := K.frontierSubcomplex (closedBall (0 : V3) 1)
  have hJ : J.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hJS : J.space = sphere (0 : V3) 1 := by
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKD,
      frontier_closedBall _ one_ne_zero]
  have hbK : PolyhedralPLInCharts e b.map K.space := hKD.symm ▸ b.piecewiseAffine
  have hbJ : PolyhedralPLInCharts e b.map J.space :=
    b.piecewiseAffine.restrict_finite J hJ (hJS.subset.trans sphere_subset_closedBall)
  obtain ⟨P, hP, hPs⟩ :=
    (hbK.finitePiecewiseAffineOn_comp K hK hF).exists_finite_triangulation_image
  obtain ⟨Q, hQ, hQs⟩ :=
    (hbJ.finitePiecewiseAffineOn_comp J hJ hF).exists_finite_triangulation_image
  refine ⟨P, Q, hP, hQ, ?_, ?_⟩
  · rw [hPs, hKD, image_comp, hmapD]
  · rw [hQs, hJS, image_comp, hmapS]

end PoincareConjecture.M76
