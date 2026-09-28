import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.BoundaryLocalHomeomorph
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteConvexDomain
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Cube" => closedBall (0 : V3) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "atlas" => (fun _ : Unit => OpenPartialHomeomorph.refl V3)

private theorem unit_cube_plDomain : PLDomain atlas Cube := by
  have hb : IsFinitePLBallPair V3 Cube (frontier Cube) := by
    rw [frontier_closedBall _ one_ne_zero]
    exact isFinitePLBallPair_unit_cube
  obtain ⟨K, _, hK, hKs, _, _⟩ := hb.exists_finite_carrier_and_rim_complexes
  have hp : (1 : V3) ∈ frontier Cube := by
    rw [frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
    simp
  have hm : (-1 : V3) ∈ frontier Cube := by
    rw [frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
    simp
  exact K.plDomain_convex_of_frontier_points hK (isCompact_closedBall _ _)
    (convex_closedBall _ _) ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
    hKs hp hm (by intro h; have hh := congrFun h 0; norm_num at hh)

theorem ChartwisePLSphere.isClopen_in_frontier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q S : Set X}
    (sph : ChartwisePLSphere e S) (he : PLDomain e Q) (hSQ : S ⊆ frontier Q) :
    IsClopen ((Subtype.val : frontier Q → X) ⁻¹' S) := by
  let H : Sphere ≃ₜ frontier Cube := Homeomorph.setCongr (frontier_closedBall _ one_ne_zero).symm
  have hid : PolyhedralPLInCharts atlas (id : V3 → V3) Sphere := by
    obtain ⟨_, K, _, _, hK, hKs⟩ :=
      (isFinitePLBallPair_unit_cube (ι := Fin 3)).exists_finite_carrier_and_rim_complexes
    refine ⟨continuous_id.continuousOn, ?_⟩
    intro x
    refine ⟨(), K, univ, hK, hKs.subset, isOpen_univ, mem_univ _, ?_, ?_, ?_⟩
    · rintro _ ⟨z, _, rfl⟩
      exact hKs.symm ▸ z.property
    · exact fun _ _ ↦ mem_univ _
    · exact ⟨K, hK, rfl, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)⟩
  let b : C(frontier Cube, frontier Q) := {
    toFun := fun z ↦ ⟨sph.parametrization (H.symm z), hSQ (sph.parametrization (H.symm z)).property⟩
    continuous_toFun := (continuous_subtype_val.comp
      (sph.parametrization.continuous.comp H.symm.continuous)).subtype_mk _ }
  have hbval (z : Sphere) : sph.map z = (b (H z) : X) := by
    change sph.map z = (sph.parametrization (H.symm (H z)) : X)
    rw [H.symm_apply_apply]
    exact sph.map_eq z
  have hbinj : IsLocallyInjective b := by
    intro x
    refine ⟨univ, isOpen_univ, mem_univ _, ?_⟩
    intro y _ z _ hyz
    apply H.symm.injective
    apply sph.parametrization.injective
    exact Subtype.ext (congrArg (fun w : frontier Q ↦ (w : X)) hyz)
  have hlocal := isLocalHomeomorph_frontier_of_polyhedral_model unit_cube_plDomain he H
    id hid (fun _ ↦ rfl) sph.map sph.piecewiseAffine b hbval hbinj
  have hrange : range b = (Subtype.val : frontier Q → X) ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (sph.parametrization (H.symm y)).property
    · intro hz
      refine ⟨H (sph.parametrization.symm ⟨z, hz⟩), ?_⟩
      apply Subtype.ext
      change (sph.parametrization (H.symm (H (sph.parametrization.symm ⟨z, hz⟩))) : X) = z
      rw [H.symm_apply_apply, sph.parametrization.apply_symm_apply]
  exact ⟨sph.isCompact.isClosed.preimage continuous_subtype_val,
    hrange ▸ hlocal.isOpenMap.isOpen_range⟩

end PoincareConjecture.M76
