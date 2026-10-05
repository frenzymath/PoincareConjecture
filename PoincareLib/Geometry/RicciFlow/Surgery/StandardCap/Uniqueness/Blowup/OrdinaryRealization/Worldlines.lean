import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.OrdinaryRealization.SliceCylinders
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Mathlib.NormalizedInterval

/-!
# Maximal worldlines of the actual standard flow

Morgan-Tian, Theorem 12.28, pp. 323-324, through the worldline hypothesis
of Theorem 11.1. The normalized domain is the exact affine inverse image
of the actual time domain; empty slices prove its maximality.
See `tasks/M35/derivations/04-generalized-realization.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- Theorem 11.1's maximal worldline on the full normalized ordinary-flow domain.
Used in Theorem 12.28, pp. 323-324. -/
noncomputable def maximalWorldline {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (hJ : J.OrdConnected) {a : ℝ} (ha : a ∈ J) (x : (slice J a).carrier)
    (Q : ℝ) (hQ : 0 < Q) (T : ℝ)
    (htime : ∀ s ∈ Icc (-T) 0, a + s / Q ∈ J) :
    GeneralizedMaximalBackwardFlowLine (generalizedFlow F) ⟨a, x⟩ Q T where
  maximal_interval := (fun s => a + s / Q) ⁻¹' J
  maximal_interval_mem_zero := by simpa only [mem_preimage, zero_div, add_zero] using ha
  maximal_interval_ordConnected := hJ.preimage_mono
    (fun _ _ h => add_le_add le_rfl (div_le_div_of_nonneg_right h hQ.le))
  embedding := sliceCylinder F ha Q hQ ((fun s => a + s / Q) ⁻¹' J) {x}
    (fun _ hs => hs)
  zero_identity := sliceCylinder_zero_identity F ha Q hQ _ _ _ _ x
  requested_interval_subset := htime
  maximal I' e' _ hI _ := by
    apply Subset.antisymm _ hI
    intro s hs
    exact (e'.forward s hs x).property

/-- Theorem 11.1's requested survival on an actual finite ordinary-flow slab.
Used in Theorem 12.28, pp. 323-324. -/
noncomputable def maximalWorldlineIco {L : ℝ}
    (F : RicciFlow 3 StandardCapSpace (Ico 0 L)) {a : ℝ} (ha : a ∈ Ico 0 L)
    (x : (slice (Ico 0 L) a).carrier) (Q : ℝ) (hQ : 0 < Q) (T : ℝ)
    (hT : T ≤ Q * a) :
    GeneralizedMaximalBackwardFlowLine (generalizedFlow F) ⟨a, x⟩ Q T :=
  maximalWorldline F ordConnected_Ico ha x Q hQ T
    (fun _ hs => add_div_mem_Ico_of_mem_Icc ha hQ hT hs)

end PoincareMT.M35.OrdinaryRealization
