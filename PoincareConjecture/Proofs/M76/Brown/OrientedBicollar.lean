import PoincareConjecture.Proofs.M76.Brown.BicollarSeparation









set_option autoImplicit false

open Set

namespace BrownCollar

variable {B : Type*} [TopologicalSpace B]


def reverseBicollar : (B × Ioo (-1 : ℝ) 1) ≃ₜ (B × Ioo (-1 : ℝ) 1) where
  toFun z := (z.1, ⟨-(z.2 : ℝ), by
    constructor <;> linarith [z.2.property.1, z.2.property.2]⟩)
  invFun z := (z.1, ⟨-(z.2 : ℝ), by
    constructor <;> linarith [z.2.property.1, z.2.property.2]⟩)
  left_inv z := Prod.ext rfl (Subtype.ext (neg_neg (z.2 : ℝ)))
  right_inv z := Prod.ext rfl (Subtype.ext (neg_neg (z.2 : ℝ)))
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {X : Type*} [TopologicalSpace X] {S C U V : Set X}




theorem exists_bicollar_oriented_to_components [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [ConnectedSpace S]
    (hS : IsClosed S) (hC : IsOpen C) (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X))
    (hclass : ∀ x ∈ Sᶜ, connectedComponentIn Sᶜ x = U ∨ connectedComponentIn Sᶜ x = V) :
    ∃ G : (S × Ioo (-1 : ℝ) 1) ≃ₜ C,
      (∀ s, (G (bicollarBase s) : X) = (s : X)) ∧
      (∀ z, (z.2 : ℝ) < 0 → (G z : X) ∈ U) ∧
      (∀ z, 0 < (z.2 : ℝ) → (G z : X) ∈ V) := by
  classical
  let s0 : S := Classical.choice inferInstance
  let zp : S × Ioo (-1 : ℝ) 1 := (s0, ⟨1 / 2, by constructor <;> norm_num⟩)
  let zm : S × Ioo (-1 : ℝ) 1 := (s0, ⟨-(1 / 2), by constructor <;> norm_num⟩)
  have hp : 0 < (zp.2 : ℝ) := by norm_num [zp]
  have hm : (zm.2 : ℝ) < 0 := by norm_num [zm]
  have hpout : (H zp : X) ∈ Sᶜ := (bicollar_point_mem_overlap H hbase zp (ne_of_gt hp)).1
  have hmout : (H zm : X) ∈ Sᶜ := (bicollar_point_mem_overlap H hbase zm (ne_of_lt hm)).1
  have hP : range (positiveBicollarMap H) ⊆ connectedComponentIn Sᶜ (H zp : X) :=
    (isConnected_range_positiveBicollarMap H).isPreconnected.subset_connectedComponentIn
      (mem_range_positiveBicollarMap H zp hp) (range_positiveBicollarMap_subset H hbase)
  have hM : range (negativeBicollarMap H) ⊆ connectedComponentIn Sᶜ (H zm : X) :=
    (isConnected_range_negativeBicollarMap H).isPreconnected.subset_connectedComponentIn
      (mem_range_negativeBicollarMap H zm hm) (range_negativeBicollarMap_subset H hbase)
  have hsep := opposite_bicollar_points_separated hS hC H hbase zp zm hp hm
  rcases hclass (H zm) hmout with hMU | hMV
  · have hPV : connectedComponentIn Sᶜ (H zp : X) = V := by
      rcases hclass (H zp) hpout with hPU | hPV
      · exfalso
        apply hsep
        rw [hPU, ← hMU]
        exact mem_connectedComponentIn hmout
      · exact hPV
    refine ⟨H, hbase, ?_, ?_⟩
    · intro z hz
      exact hMU ▸ hM (mem_range_negativeBicollarMap H z hz)
    · intro z hz
      exact hPV ▸ hP (mem_range_positiveBicollarMap H z hz)
  · have hPU : connectedComponentIn Sᶜ (H zp : X) = U := by
      rcases hclass (H zp) hpout with hPU | hPV
      · exact hPU
      · exfalso
        apply hsep
        rw [hPV, ← hMV]
        exact mem_connectedComponentIn hmout
    let G := (reverseBicollar (B := S)).trans H
    refine ⟨G, ?_, ?_, ?_⟩
    · intro s
      have hr : reverseBicollar (bicollarBase s) = bicollarBase s :=
        Prod.ext rfl (Subtype.ext (neg_zero : -(0 : ℝ) = 0))
      change (H (reverseBicollar (bicollarBase s)) : X) = (s : X)
      rw [hr, hbase]
    · intro z hz
      have hzn : 0 < ((reverseBicollar z).2 : ℝ) := neg_pos.mpr hz
      exact hPU ▸ hP (mem_range_positiveBicollarMap H (reverseBicollar z) hzn)
    · intro z hz
      have hzn : ((reverseBicollar z).2 : ℝ) < 0 := neg_neg_of_pos hz
      exact hMV ▸ hM (mem_range_negativeBicollarMap H (reverseBicollar z) hzn)

end BrownCollar
