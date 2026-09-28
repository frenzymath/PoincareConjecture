import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ConnectedRimProjection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalMiddle

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {d q : Set E} {marks : Fin 4 → E}
  (C : OriginalPrimalSectorDecomposition d q marks)

theorem OriginalPrimalSectorDecomposition.rim_inter_marks (i : Fin 4) :
    C.rim i ∩ range marks = {marks (C.order i), marks (C.order (i + 1))} := by
  apply Subset.antisymm
  · rintro x ⟨hx, j, rfl⟩
    let k := C.order.symm j
    have hj : C.order k = j := C.order.apply_symm_apply j
    by_cases hki : k = i
    · exact Or.inl (congrArg marks (hj.symm.trans (congrArg C.order hki)))
    by_cases hkn : k = i + 1
    · exact Or.inr (congrArg marks (hj.symm.trans (congrArg C.order hkn)))
    have hk : k = i + 2 ∨ k = i + 3 := by omega
    have hxop : marks j ∈ C.rim (i + 2) := by
      apply (C.rim_ball (i + 2)).1
      rcases hk with hk | hk
      · exact Or.inl (congrArg marks (hj.symm.trans (congrArg C.order hk)))
      · right
        have he : i + 2 + 1 = i + 3 := by omega
        exact congrArg marks (hj.symm.trans (congrArg C.order (hk.trans he.symm)))
    exact (disjoint_left.mp (C.rim_disjoint_opposite i) hx hxop).elim
  · intro x hx
    refine ⟨(C.rim_ball i).1 hx, ?_⟩
    rcases hx with hx | hx
    · exact ⟨C.order i, hx.symm⟩
    · exact ⟨C.order (i + 1), hx.symm⟩

theorem OriginalPrimalSectorDecomposition.rim_without_marks_nonempty
    (hm : Function.Injective marks) (i : Fin 4) :
    (C.rim i \ range marks).Nonempty := by
  have hne : marks (C.order i) ≠ marks (C.order (i + 1)) := by
    intro he
    have hi := C.order.injective (hm he)
    omega
  obtain ⟨e, _, he0, he1⟩ := (C.rim_ball i).exists_unitInterval_chart_with_endpoints hne
  let m : Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
  refine ⟨e m, (e m).property, ?_⟩
  intro hmark
  have hend := (C.rim_inter_marks i).subset ⟨(e m).property, hmark⟩
  rcases hend with h0 | h1
  · have he : e m = e 0 := Subtype.ext (h0.trans he0.symm)
    have hh := congrArg Subtype.val (e.injective he)
    norm_num [m] at hh
  · have he : e m = e 1 := Subtype.ext (h1.trans he1.symm)
    have hh := congrArg Subtype.val (e.injective he)
    norm_num [m] at hh

end PoincareConjecture.M76.OriginalTriangleCopies
