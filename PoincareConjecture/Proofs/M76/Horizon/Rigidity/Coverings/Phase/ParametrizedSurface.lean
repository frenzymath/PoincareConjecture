import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.HomotopyToCovering
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters

set_option autoImplicit false

namespace PoincareConjecture.M76

open LinearTorus

theorem exists_parametrized_torus_covering {S : Type*} [TopologicalSpace S]
    (p : ℝ) (hp : 0 < p) (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (f : C(S, AddCircle p × AddCircle p))
    (hf : Function.Injective (FundamentalGroup.map f (h 0))) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℤ) (g : C(S, AddCircle p × AddCircle p)),
      A.det ≠ 0 ∧ IsCoveringMap g ∧
      (∀ x, g x = affineIntegerMatrixMap p A (f (h 0)) (h.symm x)) ∧
      Nonempty (f.HomotopyRel g {h 0}) := by
  let f' : C(AddCircle p × AddCircle p, AddCircle p × AddCircle p) :=
    f.comp ⟨h, h.continuous⟩
  have hf' : Function.Injective (FundamentalGroup.map f' 0) := by
    rw [show f' = f.comp ⟨h, h.continuous⟩ from rfl, FundamentalGroup.map_comp]
    exact hf.comp (h.fundamentalGroupMulEquiv 0).injective
  obtain ⟨A, hA, hcover, ⟨H⟩⟩ := exists_homotopy_affine_covering p hp f' hf'
  let g : C(S, AddCircle p × AddCircle p) :=
    (affineIntegerMatrixMap p A (f (h 0))).comp ⟨h.symm, h.symm.continuous⟩
  refine ⟨A, g, hA, hcover.comp_homeomorph h.symm, fun _ => rfl, ?_⟩
  refine ⟨{
    toFun := fun z => H (z.1, h.symm z.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk
      (h.symm.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    rw [H.apply_zero]
    change f (h (h.symm x)) = f x
    rw [h.apply_symm_apply]
  · intro x
    exact H.apply_one (h.symm x)
  · intro t x hx
    obtain rfl : x = h 0 := Set.mem_singleton_iff.mp hx
    change H (t, h.symm (h 0)) = f (h 0)
    rw [h.symm_apply_apply]
    exact H.prop t 0 (Set.mem_singleton 0)

end PoincareConjecture.M76
