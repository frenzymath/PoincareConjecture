import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Identification
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology

/-!
# One fixed sphere parameter for M59

M02's cube-to-sphere quotient collapses exactly the cube boundary. In dimension
two it gives the common parameter required by all normalized M59 families.
Source: Morgan--Tian Claim 18.16 and Definition 18.17, printed p. 430.
-/

set_option autoImplicit false

open scoped Topology unitInterval

namespace PoincareMT

/-- The M59 sphere parameter exists with literal exact fibers.
Source: Morgan--Tian Claim 18.16 and Definition 18.17, printed p. 430. -/
theorem m59SphereQuotient_nonempty : Nonempty M59SphereQuotient := by
  obtain ⟨q, hq, hfiber⟩ := Proofs.M02.exists_cube_sphere_quotient_of_card_eq
    (N := Fin 2) (ι := Fin 3) (by simp)
  have hsphere : Metric.sphere (0 : LoopAmbient) 1 = {z : LoopAmbient | ‖z‖ = 1} := by
    ext z
    simp only [Metric.mem_sphere, dist_zero_right, Set.mem_ofPred_eq]
  let e : Metric.sphere (0 : LoopAmbient) 1 ≃ₜ LoopTwoSphere :=
    Homeomorph.setCongr hsphere
  let Q : C((Fin 2 → I), LoopTwoSphere) :=
    ⟨fun t => e (q t), e.continuous.comp q.continuous⟩
  have hzero : (fun _ : Fin 2 => (0 : I)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  refine ⟨{
    map := Q
    pole := Q (fun _ => 0)
    surjective := e.surjective.comp hq.surjective
    boundary_collapsed := ?_
    exact_fibers := ?_ }⟩
  · intro t ht
    exact congrArg e ((hfiber t (fun _ => 0)).mpr (Or.inr ⟨ht, hzero⟩))
  · intro t s
    exact e.injective.eq_iff.trans (hfiber t s)

/-- Choose the sphere parameter once, independently of the manifold and class.
Source: Morgan--Tian Claim 18.16 and Definition 18.17, printed p. 430. -/
noncomputable def m59SphereQuotient : M59SphereQuotient :=
  Classical.choice m59SphereQuotient_nonempty

end PoincareMT
