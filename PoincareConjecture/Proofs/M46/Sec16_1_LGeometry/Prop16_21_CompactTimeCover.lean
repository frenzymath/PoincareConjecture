import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M46

theorem exists_compact_of_local_time_cages
    {X : Type u} [TopologicalSpace X] {clock : X → ℝ} {Z : Set X}
    {a b : ℝ} (hclock : MapsTo clock Z (Icc a b))
    (hlocal : ∀ t ∈ Icc a b, ∃ N : Set X, IsCompact N ∧
      ∃ delta : ℝ, 0 < delta ∧ ∀ z ∈ Z, |clock z - t| < delta → z ∈ N) :
    ∃ K : Set X, IsCompact K ∧ Z ⊆ K := by
  classical
  choose N hN delta hdelta hcapture using (fun t : Icc a b => hlocal t.val t.property)
  let U (t : Icc a b) : Set ℝ := Ioo (t.val - delta t) (t.val + delta t)
  obtain ⟨cover, hcover⟩ := isCompact_Icc.elim_finite_subcover U
    (fun _ => isOpen_Ioo) (by
      intro t ht
      apply mem_iUnion.mpr
      refine ⟨⟨t, ht⟩, ?_⟩
      constructor <;> linarith [hdelta ⟨t, ht⟩])
  refine ⟨⋃ t ∈ cover, N t, cover.isCompact_biUnion (fun t _ => hN t), ?_⟩
  intro z hz
  obtain ⟨t, ht, htime⟩ := mem_iUnion₂.mp (hcover (hclock hz))
  apply mem_iUnion₂.mpr
  refine ⟨t, ht, hcapture t z hz ?_⟩
  exact abs_lt.mpr ⟨by linarith [htime.1], by linarith [htime.2]⟩

end PoincareConjecture.Proofs.M46
