import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinder
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set Metric

namespace Geometry

variable (ι κ : Type*) [Fintype ι]

noncomputable def coordinateCylinderProduct :
    coordinateCylinder (Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)) ≃ₜ
      (closedBall (0 : ι → ℝ) 1 × (κ → ℝ)) where
  toFun x := (⟨fun i => x.1 (Sum.inl i), by
    rw [mem_closedBall_zero_iff]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    exact x.2 _ (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩,
    fun j => x.1 (Sum.inr j))
  invFun y := ⟨Sum.elim y.1.1 y.2, by
    rintro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact (norm_le_pi_norm y.1.1 j).trans (mem_closedBall_zero_iff.mp y.1.2)⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  right_inv y := rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_pi fun i => (continuous_apply (Sum.inl i)).comp continuous_subtype_val
    · exact continuous_pi fun j => (continuous_apply (Sum.inr j)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
    | inr j => exact (continuous_apply j).comp continuous_snd

theorem coordinateCylinderProduct_frontier
    (x : coordinateCylinder (Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)))
    (hx : (x : (ι ⊕ κ) → ℝ) ∈
      frontier (coordinateCylinder (Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)))) :
    ‖((coordinateCylinderProduct ι κ x).1 : ι → ℝ)‖ = 1 := by
  have hle := mem_closedBall_zero_iff.mp (coordinateCylinderProduct ι κ x).1.2
  apply le_antisymm hle
  by_contra h
  have hlt : ‖fun i => x.1 (Sum.inl i)‖ < 1 := lt_of_not_ge h
  let U : Set ((ι ⊕ κ) → ℝ) := {y | ‖fun i : ι => y (Sum.inl i)‖ < 1}
  have hU : IsOpen U := isOpen_lt
    (continuous_pi fun i => continuous_apply (Sum.inl i)).norm continuous_const
  have hsub : U ⊆ coordinateCylinder
      (Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)) := by
    intro y hy i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact (norm_le_pi_norm (fun i : ι => y (Sum.inl i)) j).trans hy.le
  exact hx.2 (mem_interior.mpr ⟨U, hsub, hU, hlt⟩)

variable [Fintype κ]

theorem coordinateCylinderProduct_displacement
    (G : (closedBall (0 : ι → ℝ) 1 × (κ → ℝ)) ≃ₜ
      (closedBall (0 : ι → ℝ) 1 × (κ → ℝ))) {C : ℝ}
    (hC : ∀ a v, ‖(G (a, v)).2 - v‖ ≤ C)
    (x : coordinateCylinder (Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ))) :
    ‖((coordinateCylinderProduct ι κ).symm (G (coordinateCylinderProduct ι κ x)) :
      (ι ⊕ κ) → ℝ) - x‖ ≤ max 2 C := by
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (by norm_num))).mpr
  intro i
  rcases i with i | j
  · have ha := mem_closedBall_zero_iff.mp (G (coordinateCylinderProduct ι κ x)).1.2
    have hb := mem_closedBall_zero_iff.mp (coordinateCylinderProduct ι κ x).1.2
    apply (norm_sub_le _ _).trans
    exact (add_le_add ((norm_le_pi_norm _ i).trans ha)
      ((norm_le_pi_norm _ i).trans hb)).trans (by norm_num)
  · exact ((norm_le_pi_norm _ j).trans
      (hC (coordinateCylinderProduct ι κ x).1 (coordinateCylinderProduct ι κ x).2)).trans
      (le_max_right _ _)

end Geometry
