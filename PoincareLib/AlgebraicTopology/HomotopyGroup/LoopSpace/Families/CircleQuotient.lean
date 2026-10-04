import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Identification
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.CubeBoundaryQuotient

/-!
# One exact circle parameter

The one-dimensional instance of M02's cube quotient identifies the interval
endpoints and no other points. It supplies a common circle coordinate for
the loop-space adjunction. Source: MT Claim 18.16, printed p. 430.
-/

set_option autoImplicit false

open scoped Topology unitInterval

namespace PoincareMT

/-- An exact cube-boundary quotient onto the loop circle exists.
Source: MT Claim 18.16, printed p. 430; Hatcher, Section 4.1, p. 340. -/
theorem m59CircleQuotient_nonempty :
    Nonempty (Proofs.M59.CubeBoundaryQuotient (Fin 1) LoopCircle) := by
  obtain ⟨q, hq, hfiber⟩ := Proofs.M02.exists_cube_sphere_quotient_of_card_eq
    (N := Fin 1) (ι := Fin 2) (by simp)
  have hsphere : Metric.sphere (0 : LoopPlane) 1 = {z : LoopPlane | ‖z‖ = 1} := by
    ext z
    simp only [Metric.mem_sphere, dist_zero_right, Set.mem_ofPred_eq]
  let e : Metric.sphere (0 : LoopPlane) 1 ≃ₜ LoopCircle := Homeomorph.setCongr hsphere
  let Q : C((Fin 1 → I), LoopCircle) :=
    ⟨fun v => e (q v), e.continuous.comp q.continuous⟩
  have hz : (fun _ : Fin 1 => (0 : I)) ∈ Cube.boundary (Fin 1) := ⟨0, Or.inl rfl⟩
  refine ⟨{
    map := Q
    pole := Q (fun _ => 0)
    surjective := e.surjective.comp hq.surjective
    boundary_collapsed := ?_
    exact_fibers := ?_ }⟩
  · intro v hv
    exact congrArg e ((hfiber v (fun _ => 0)).mpr (Or.inr ⟨hv, hz⟩))
  · intro v w
    exact e.injective.eq_iff.trans (hfiber v w)

/-- Choose the same exact circle parameter for all spaces and classes.
Source: MT Claim 18.16, printed p. 430. -/
noncomputable def m59CircleQuotient : Proofs.M59.CubeBoundaryQuotient (Fin 1) LoopCircle :=
  Classical.choice m59CircleQuotient_nonempty

end PoincareMT
