import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# An open real height with constant boundary excludes compact closure

A continuous height on a compact closure attains both extrema. If its
image on the open set is open, neither extremum can lie there. Constant
boundary values then force an interior maximum, a contradiction. This
is the compact-side argument in Morgan--Tian Claim 10.8, p. 254,
expanded in M28 derivation 120.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace Poincare

/-- A nonempty open set with an open real height image and constant
boundary height has noncompact closure. Continuity is required only on
that closure. Source: M28 derivation 120, the open-height extremum proof. -/
theorem not_isCompact_closure_of_open_height
    {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsOpen C)
    (hne : C.Nonempty) {f : X → ℝ} (hf : ContinuousOn f (closure C))
    (himage : IsOpen (f '' C)) {c : ℝ}
    (hfront : ∀ x ∈ frontier C, f x = c) : ¬ IsCompact (closure C) := by
  intro hcompact
  have hmaxout (z : X) (hz : IsMaxOn f (closure C) z) : z ∉ C := by
    intro hzC
    obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (himage.mem_nhds (mem_image_of_mem f hzC))
    have hv : (f z + b) / 2 ∈ Ioo a b :=
      ⟨by linarith [hab.1, hab.2], by linarith [hab.2]⟩
    obtain ⟨y, hy, heq⟩ := hsub hv
    have hle := hz (subset_closure hy)
    change f y ≤ f z at hle
    rw [heq] at hle
    linarith [hab.2]
  have hminout (z : X) (hz : IsMinOn f (closure C) z) : z ∉ C := by
    intro hzC
    obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (himage.mem_nhds (mem_image_of_mem f hzC))
    have hv : (a + f z) / 2 ∈ Ioo a b :=
      ⟨by linarith [hab.1], by linarith [hab.1, hab.2]⟩
    obtain ⟨y, hy, heq⟩ := hsub hv
    have hle := hz (subset_closure hy)
    change f z ≤ f y at hle
    rw [heq] at hle
    linarith [hab.1]
  obtain ⟨z, hz, hzmax⟩ := hcompact.exists_isMaxOn (hne.mono subset_closure) hf
  obtain ⟨w, hw, hwmin⟩ := hcompact.exists_isMinOn (hne.mono subset_closure) hf
  have hzc : f z = c := hfront z (hC.frontier_eq.symm ▸ ⟨hz, hmaxout z hzmax⟩)
  have hwc : f w = c := hfront w (hC.frontier_eq.symm ▸ ⟨hw, hminout w hwmin⟩)
  obtain ⟨x, hx⟩ := hne
  have hxc : f x = c := le_antisymm ((hzmax (subset_closure hx)).trans_eq hzc)
    (hwc.symm.trans_le (hwmin (subset_closure hx)))
  apply hmaxout x _ hx
  intro y hy
  exact (hzmax hy).trans_eq (hzc.trans hxc.symm)

end Poincare
