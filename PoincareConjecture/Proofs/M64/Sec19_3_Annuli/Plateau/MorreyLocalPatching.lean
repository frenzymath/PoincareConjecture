import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

theorem m64Morrey_patch_representatives
    {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {mu : Measure X}
    [mu.IsOpenPosMeasure] [TopologicalSpace Y] [T2Space Y]
    {O : Set X} {u : X → Y}
    (hlocal : ∀ a ∈ O, ∃ S : Set X, IsOpen S ∧ a ∈ S ∧ S ⊆ O ∧
      ∃ v : X → Y, ContinuousOn v S ∧ v =ᵐ[mu.restrict S] u) :
    ∃ U : X → Y, ContinuousOn U O ∧ U =ᵐ[mu.restrict O] u := by
  classical
  choose S hS hmem hsub v hv hae using fun a : O => hlocal a a.property
  have hagree (a b : O) : EqOn (v a) (v b) (S a ∩ S b) := by
    have h1 : v a =ᵐ[mu.restrict (S a ∩ S b)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hae a)
    have h2 : v b =ᵐ[mu.restrict (S a ∩ S b)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hae b)
    exact Measure.eqOn_open_of_ae_eq (h1.trans h2.symm)
      ((hS a).inter (hS b)) ((hv a).mono inter_subset_left) ((hv b).mono inter_subset_right)
  let U : X → Y := fun x => if hx : x ∈ O then v ⟨x, hx⟩ x else u x
  have hUv (a : O) : EqOn U (v a) (S a) := by
    intro x hx
    dsimp only [U]
    rw [dif_pos (hsub a hx)]
    exact hagree ⟨x, hsub a hx⟩ a ⟨hmem ⟨x, hsub a hx⟩, hx⟩
  have hcont : ContinuousOn U O := by
    intro x hx
    let a : O := ⟨x, hx⟩
    apply ContinuousAt.continuousWithinAt
    apply ((hv a).continuousAt ((hS a).mem_nhds (hmem a))).congr_of_eventuallyEq
    exact Filter.mem_of_superset ((hS a).mem_nhds (hmem a)) (hUv a)
  have hUae (a : O) : U =ᵐ[mu.restrict (S a)] u := by
    have hh : U =ᵐ[mu.restrict (S a)] v a :=
      Filter.mem_of_superset (ae_restrict_mem (hS a).measurableSet) (hUv a)
    exact hh.trans (hae a)
  obtain ⟨T, hT, hcover⟩ := (HereditarilyLindelofSpace.isLindelof O).elim_countable_subcover
    S hS (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  refine ⟨U, hcont, ae_restrict_of_ae_restrict_of_subset hcover ?_⟩
  exact (ae_eq_restrict_biUnion_iff S hT U u).mpr fun a _ => hUae a

end PoincareConjecture
