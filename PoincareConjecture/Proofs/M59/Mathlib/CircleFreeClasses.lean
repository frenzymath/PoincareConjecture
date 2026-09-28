import PoincareConjecture.Proofs.M59.Mathlib.FreeLoopAbelian
import PoincareConjecture.Proofs.M59.Mathlib.CubeBoundaryQuotient









set_option autoImplicit false

open scoped Topology unitInterval

namespace PoincareConjecture.Proofs.M59.CubeBoundaryQuotient

variable {S X : Type*} [TopologicalSpace S] [T2Space S] [TopologicalSpace X]
  (q : CubeBoundaryQuotient (Fin 1) S) {x : X}



theorem homotopic_of_descend_homotopic
    (hcomm : ∀ a b : FundamentalGroup X x, a * b = b * a)
    {f g : GenLoop (Fin 1) X x} (h : (q.descend f).Homotopic (q.descend g)) :
    GenLoop.Homotopic f g := by
  obtain ⟨H⟩ := h
  let p := genLoopEquivOfUnique (Fin 1) f
  let r := genLoopEquivOfUnique (Fin 1) g
  let K : p.toContinuousMap.Homotopy r.toContinuousMap := {
    toFun v := H (v.1, q.map (fun _ => v.2))
    continuous_toFun := by fun_prop
    map_zero_left := fun t => (H.apply_zero _).trans (q.descend_map f _)
    map_one_left := fun t => (H.apply_one _).trans (q.descend_map g _) }
  have hK : ∀ t, K (t, 0) = K (t, 1) := by
    intro t
    change H (t, q.map (fun _ => 0)) = H (t, q.map (fun _ => 1))
    rw [q.boundary_collapsed _ ⟨0, Or.inl rfl⟩,
      q.boundary_collapsed _ ⟨0, Or.inr rfl⟩]
  have hp := Path.homotopic_of_free_homotopy hcomm p r K hK
  have he : (⟦f⟧ : HomotopyGroup (Fin 1) X x) = ⟦g⟧ :=
    (homotopyGroupEquivFundamentalGroupOfUnique (Fin 1)).injective (Quotient.sound hp)
  exact Quotient.exact he



theorem descend_homotopic_iff
    (hcomm : ∀ a b : FundamentalGroup X x, a * b = b * a)
    {f g : GenLoop (Fin 1) X x} :
    (q.descend f).Homotopic (q.descend g) ↔ GenLoop.Homotopic f g :=
  ⟨q.homotopic_of_descend_homotopic hcomm, q.descend_homotopic⟩

end PoincareConjecture.Proofs.M59.CubeBoundaryQuotient
