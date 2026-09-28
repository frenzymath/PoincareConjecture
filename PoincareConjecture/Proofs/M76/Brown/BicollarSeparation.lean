import PoincareConjecture.Proofs.M76.Brown.BicollarSignSeparation
import PoincareConjecture.Proofs.M76.Brown.BicollarOpenHalves
import PoincareConjecture.Proofs.M76.Brown.ComplementComponentNeighborhood










set_option autoImplicit false

open Set

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X] {S C : Set X}





theorem exists_bicollar_complement_components [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [ConnectedSpace S]
    (hS : IsClosed S) (hC : IsOpen C) (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X)) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Sᶜ ∧ frontier U = S ∧ frontier V = S ∧
      ∀ x ∈ Sᶜ, connectedComponentIn Sᶜ x = U ∨ connectedComponentIn Sᶜ x = V := by
  classical
  let s0 : S := Classical.choice inferInstance
  let zp : S × Ioo (-1 : ℝ) 1 := (s0, ⟨1 / 2, by constructor <;> norm_num⟩)
  let zm : S × Ioo (-1 : ℝ) 1 := (s0, ⟨-(1 / 2), by constructor <;> norm_num⟩)
  have hp : 0 < (zp.2 : ℝ) := by norm_num [zp]
  have hm : (zm.2 : ℝ) < 0 := by norm_num [zm]
  have hpout : (H zp : X) ∈ Sᶜ := (bicollar_point_mem_overlap H hbase zp (ne_of_gt hp)).1
  have hmout : (H zm : X) ∈ Sᶜ := (bicollar_point_mem_overlap H hbase zm (ne_of_lt hm)).1
  let U := connectedComponentIn Sᶜ (H zp : X)
  let V := connectedComponentIn Sᶜ (H zm : X)
  have hP : range (positiveBicollarMap H) ⊆ U :=
    (isConnected_range_positiveBicollarMap H).isPreconnected.subset_connectedComponentIn
      (mem_range_positiveBicollarMap H zp hp) (range_positiveBicollarMap_subset H hbase)
  have hM : range (negativeBicollarMap H) ⊆ V :=
    (isConnected_range_negativeBicollarMap H).isPreconnected.subset_connectedComponentIn
      (mem_range_negativeBicollarMap H zm hm) (range_negativeBicollarMap_subset H hbase)
  have hdisjoint : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro y hyU hyV
    have heq : U = V := (connectedComponentIn_eq hyU).trans (connectedComponentIn_eq hyV).symm
    exact opposite_bicollar_points_separated hS hC H hbase zp zm hp hm
      (heq.symm.subset (mem_connectedComponentIn hmout))
  have hSC : S ⊆ C := by
    intro x hx
    have hmem := (H (bicollarBase ⟨x, hx⟩)).property
    simpa only [hbase] using hmem
  have hunion : U ∪ V = Sᶜ := by
    apply subset_antisymm
    · exact union_subset (connectedComponentIn_subset Sᶜ (H zp : X))
        (connectedComponentIn_subset Sᶜ (H zm : X))
    · intro x hx
      obtain ⟨y, hyD, hyC⟩ :=
        complement_component_meets_neighborhood hS ⟨s0.val, s0.property⟩ hC hSC hx
      let z := H.symm ⟨y, hyC⟩
      have hzy : (H z : X) = y := congrArg Subtype.val (H.apply_symm_apply ⟨y, hyC⟩)
      have hzne : (z.2 : ℝ) ≠ 0 := by
        intro hz
        have hyS : y ∈ S := (bicollarHeight_eq_zero_iff H hbase ⟨y, hyC⟩).mp hz
        exact (connectedComponentIn_subset Sᶜ x hyD) hyS
      rcases lt_or_gt_of_ne hzne with hzneg | hzpos
      · have hyV : y ∈ V := hzy ▸ hM (mem_range_negativeBicollarMap H z hzneg)
        have heq : connectedComponentIn Sᶜ x = V :=
          (connectedComponentIn_eq hyD).trans (connectedComponentIn_eq hyV).symm
        exact Or.inr (heq.subset (mem_connectedComponentIn hx))
      · have hyU : y ∈ U := hzy ▸ hP (mem_range_positiveBicollarMap H z hzpos)
        have heq : connectedComponentIn Sᶜ x = U :=
          (connectedComponentIn_eq hyD).trans (connectedComponentIn_eq hyU).symm
        exact Or.inl (heq.subset (mem_connectedComponentIn hx))
  have hfrontU : frontier U = S := by
    refine subset_antisymm (frontier_complement_component_subset hS hpout) ?_
    intro x hx
    refine ⟨closure_mono hP (base_subset_closure_positiveBicollarMap H hbase hx), ?_⟩
    intro hxI
    exact (connectedComponentIn_subset Sᶜ (H zp : X) (interior_subset hxI)) hx
  have hfrontV : frontier V = S := by
    refine subset_antisymm (frontier_complement_component_subset hS hmout) ?_
    intro x hx
    refine ⟨closure_mono hM (base_subset_closure_negativeBicollarMap H hbase hx), ?_⟩
    intro hxI
    exact (connectedComponentIn_subset Sᶜ (H zm : X) (interior_subset hxI)) hx
  refine ⟨U, V, hS.isOpen_compl.connectedComponentIn, hS.isOpen_compl.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr hpout,
    isConnected_connectedComponentIn_iff.mpr hmout, hdisjoint, hunion, hfrontU, hfrontV, ?_⟩
  intro x hx
  rcases hunion.symm.subset hx with hxU | hxV
  · exact Or.inl (connectedComponentIn_eq hxU).symm
  · exact Or.inr (connectedComponentIn_eq hxV).symm

end BrownCollar
