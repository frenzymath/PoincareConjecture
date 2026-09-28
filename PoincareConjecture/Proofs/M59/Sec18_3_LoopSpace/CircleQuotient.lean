import PoincareConjecture.Definitions.M59LoopIdentification
import PoincareConjecture.Proofs.M02.CubeSphere
import PoincareConjecture.Proofs.M59.Mathlib.CubeBoundaryQuotient

set_option autoImplicit false

open scoped Topology unitInterval

namespace PoincareConjecture

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

noncomputable def m59CircleQuotient : Proofs.M59.CubeBoundaryQuotient (Fin 1) LoopCircle :=
  Classical.choice m59CircleQuotient_nonempty

end PoincareConjecture
