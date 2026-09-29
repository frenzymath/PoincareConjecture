/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Source: https://github.com/mccorvie/classification-of-surfaces
JordanCurve/Counting.lean
Comparison revision: e3c7230fe78d7b056a415d9ecae6f77887046b32.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Connected.Clopen

namespace Poincare.Topology.Plane.Jordan.Counting

open Set

variable {X : Type*} [TopologicalSpace X]

theorem nat_card_connectedComponents_eq_two
    (a b : X) (hab : ConnectedComponents.mk a ≠ ConnectedComponents.mk b)
    (hcover : ∀ x : X, ConnectedComponents.mk x = ConnectedComponents.mk a
                     ∨ ConnectedComponents.mk x = ConnectedComponents.mk b) :
    Nat.card (ConnectedComponents X) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨ConnectedComponents.mk a, ConnectedComponents.mk b, hab, ?_⟩
  rw [eq_univ_iff_forall]
  intro z
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
  rcases hcover x with h | h
  · exact mem_insert_iff.mpr (Or.inl h)
  · exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr h))

theorem connectedComponents_subtype_eq_iff {S : Set X} {x y : X}
    (hx : x ∈ S) (hy : y ∈ S) :
    ConnectedComponents.mk (⟨x, hx⟩ : S) = ConnectedComponents.mk (⟨y, hy⟩ : S)
      ↔ connectedComponentIn S x = connectedComponentIn S y := by
  rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image hy,
    (image_injective.mpr Subtype.coe_injective).eq_iff,
    ← ConnectedComponents.coe_eq_coe]

end Poincare.Topology.Plane.Jordan.Counting
