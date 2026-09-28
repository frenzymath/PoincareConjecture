import PoincareConjecture.Proofs.M76.Brown.BicollarHeightSign
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false

open Set SignType

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X] {S C : Set X}




theorem exists_bicollar_side_sign [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    [ConnectedSpace S] (hS : IsClosed S) (hC : IsOpen C)
    (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X)) :
    ∃ a : X → SignType, ContinuousOn a Sᶜ ∧ ∃ u : SignType, u ≠ 0 ∧
      (∀ z : S × Ioo (-1 : ℝ) 1, 0 < (z.2 : ℝ) → a (H z) = u) ∧
      (∀ z : S × Ioo (-1 : ℝ) 1, (z.2 : ℝ) < 0 → a (H z) = -u) := by
  classical
  let s0 : S := Classical.choice inferInstance
  let : Nonempty X := ⟨s0.val⟩
  let : PreconnectedSpace (Ioo (-1 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  obtain ⟨a0, a1, ha0, ha1, hcompat⟩ := exists_bicollar_sign_section hS hC H hbase
  have ha1H : Continuous (fun z : S × Ioo (-1 : ℝ) 1 => a1 (H z)) :=
    ha1.comp_continuous (continuous_subtype_val.comp H.continuous) (fun z => (H z).property)
  let u : SignTypeˣ := a1 (H (bicollarBase s0))
  have hconst (z : S × Ioo (-1 : ℝ) 1) : a1 (H z) = u :=
    (inferInstance : PreconnectedSpace (S × Ioo (-1 : ℝ) 1)).constant ha1H
  refine ⟨fun x => (a0 x : SignType), Units.continuous_val.comp_continuousOn ha0,
    (u : SignType), u.ne_zero, ?_, ?_⟩
  · intro z hz
    have heq := hcompat z (ne_of_gt hz)
    rw [hconst z, sign_pos hz, one_mul] at heq
    exact heq.symm
  · intro z hz
    have heq := hcompat z (ne_of_lt hz)
    rw [hconst z, sign_neg hz, neg_one_mul] at heq
    simpa only [neg_neg] using congrArg Neg.neg heq.symm





theorem opposite_bicollar_points_separated [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [ConnectedSpace S]
    (hS : IsClosed S) (hC : IsOpen C) (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X))
    (zp zn : S × Ioo (-1 : ℝ) 1) (hp : 0 < (zp.2 : ℝ)) (hm : (zn.2 : ℝ) < 0) :
    (H zn : X) ∉ connectedComponentIn Sᶜ (H zp : X) := by
  obtain ⟨a, ha, u, hu, hpos, hneg⟩ := exists_bicollar_side_sign hS hC H hbase
  intro hmem
  have heq : a (H zp) = a (H zn) :=
    isPreconnected_connectedComponentIn.constant
      (ha.mono (connectedComponentIn_subset Sᶜ (H zp : X)))
      (mem_connectedComponentIn (bicollar_point_mem_overlap H hbase zp (ne_of_gt hp)).1)
      hmem
  rw [hpos zp hp, hneg zn hm] at heq
  exact hu (SignType.self_eq_neg_iff.mp heq)

end BrownCollar
