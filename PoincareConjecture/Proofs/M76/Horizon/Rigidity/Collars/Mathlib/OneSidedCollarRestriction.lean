import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.InducedOpenImage
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set

namespace Poincare.Topology

theorem isOpen_smaller_oneSided_collar
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {K : Set E} {r delta : ℝ} (hd : delta ≤ r)
    (c : E × ℝ → X)
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ico (0 : ℝ) r))) :
    IsOpen (c '' (K ×ˢ Ico (0 : ℝ) delta)) := by
  let P := K ×ˢ Icc (0 : ℝ) r
  let g : P → X := fun z => c z
  let V : Set P := {z | z.val.2 < delta}
  have hV : IsOpen V := isOpen_Iio.preimage (continuous_snd.comp continuous_subtype_val)
  have hsub : g '' V ⊆ c '' (K ×ˢ Ico (0 : ℝ) r) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, ⟨z.property.1, z.property.2.1, hz.trans_le hd⟩, rfl⟩
  have hrange : c '' (K ×ˢ Ico (0 : ℝ) r) ⊆ range g := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz.1, hz.2.1, hz.2.2.le⟩, rfl⟩
  have heq : g '' V = c '' (K ×ˢ Ico (0 : ℝ) delta) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, ⟨z.property.1, z.property.2.1, hz⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz.1, hz.2.1, hz.2.2.le.trans hd⟩, hz.2.2, rfl⟩
  rw [← heq]
  exact hi.isInducing.isOpen_image_of_subset_open hV ho hsub hrange

theorem exists_oneSided_collar_width_avoiding_point
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {K : Set E} {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X)
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => c z))
    {x : X} (hx : x ∉ c '' (K ×ˢ ({0} : Set ℝ))) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ r ∧ x ∉ c '' (K ×ˢ Icc (0 : ℝ) delta) := by
  by_cases hxA : x ∈ c '' (K ×ˢ Icc (0 : ℝ) r)
  · obtain ⟨z, hz, rfl⟩ := hxA
    have hzpos : 0 < z.2 := by
      apply lt_of_le_of_ne hz.2.1
      intro heq
      exact hx ⟨z, ⟨hz.1, heq.symm⟩, rfl⟩
    refine ⟨z.2 / 2, by linarith, by linarith [hz.2.2], ?_⟩
    rintro ⟨w, hw, hweq⟩
    have hwR : w ∈ K ×ˢ Icc (0 : ℝ) r :=
      ⟨hw.1, hw.2.1, by linarith [hw.2.2, hz.2.2]⟩
    have heq := congrArg (fun a : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => a.val.2)
      (hi.injective (show c (⟨w, hwR⟩ : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ))) =
        c (⟨z, hz⟩ : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ))) from hweq))
    change w.2 = z.2 at heq
    linarith [hw.2.2]
  · exact ⟨r, hr, le_rfl, hxA⟩

end Poincare.Topology
