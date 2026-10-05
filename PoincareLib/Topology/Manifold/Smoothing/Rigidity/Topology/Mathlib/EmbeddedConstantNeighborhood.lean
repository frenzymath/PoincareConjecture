import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.ContinuousOn

/-!
# Ambient neighborhoods with a constant discrete label

Transport the actual relatively open constant-label set through an
embedding and retain a prescribed ambient open neighborhood.
See rigidity016, section1, implementing Brown1962 Lemma6, pp.338--339.
-/

set_option autoImplicit false

open Set

namespace Topology.IsEmbedding

variable {P X S : Type*} [TopologicalSpace P] [TopologicalSpace X]
  [TopologicalSpace S] [DiscreteTopology S]

/-- A discrete label continuous on an open part of an embedded space
is constant on the entire embedded preimage of a smaller ambient open
neighborhood. See rigidity016, section1. -/
theorem exists_open_constant_neighborhood {b : P → X} (hb : IsEmbedding b)
    {a : P → S} {B : Set P} (hB : IsOpen B) (ha : ContinuousOn a B)
    {x : P} (hx : x ∈ B) {O : Set X} (hO : IsOpen O) (hxO : b x ∈ O) :
    ∃ U : Set X, IsOpen U ∧ b x ∈ U ∧ U ⊆ O ∧
      ∀ y, b y ∈ U → y ∈ B ∧ a y = a x := by
  let V := B ∩ a ⁻¹' {a x}
  have hV : IsOpen V := ha.isOpen_inter_preimage hB (isOpen_discrete _)
  obtain ⟨W, hW, hWV⟩ := hb.isInducing.isOpen_iff.mp hV
  have hxW : b x ∈ W := by
    change x ∈ b ⁻¹' W
    rw [hWV]
    exact ⟨hx, rfl⟩
  refine ⟨W ∩ O, hW.inter hO, ⟨hxW, hxO⟩, inter_subset_right, ?_⟩
  intro y hy
  have hyV : y ∈ V := by
    rw [← hWV]
    exact hy.1
  exact hyV

end Topology.IsEmbedding
