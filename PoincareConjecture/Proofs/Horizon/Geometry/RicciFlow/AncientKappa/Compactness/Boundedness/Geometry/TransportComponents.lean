import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.Basic

noncomputable section
set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.AncientCompactness

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [T2Space N]

def compactTransportHomeomorph {A : Set M} {B : Set N} {Q : M → N}
    (hA : IsCompact A) (hQ : ContinuousOn Q A) (hbij : BijOn Q A B) : A ≃ₜ B := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let e := hbij.equiv Q
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (hQ.domRestrict.subtype_mk _)

@[simp] theorem compactTransportHomeomorph_apply {A : Set M} {B : Set N} {Q : M → N}
    (hA : IsCompact A) (hQ : ContinuousOn Q A) (hbij : BijOn Q A B) (x : A) :
    (compactTransportHomeomorph hA hQ hbij x : N) = Q x := rfl

theorem image_connectedComponentIn_eq_of_compact_bijOn
    {A : Set M} {B : Set N} {Q : M → N}
    (hA : IsCompact A) (hQ : ContinuousOn Q A) (hbij : BijOn Q A B)
    {x : M} (hx : x ∈ A) :
    Q '' connectedComponentIn A x = connectedComponentIn B (Q x) := by
  let e := compactTransportHomeomorph hA hQ hbij
  let p : A := ⟨x, hx⟩
  have he : e '' connectedComponent p = connectedComponent (e p) := by
    simpa only [connectedComponentIn_univ, image_univ, e.surjective.range_eq] using
      e.image_connectedComponentIn (mem_univ p)
  rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image (hbij.mapsTo hx)]
  apply Subset.antisymm
  · rintro y ⟨z, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨e q, ?_, rfl⟩
    change e q ∈ connectedComponent (e p)
    rw [← he]
    exact mem_image_of_mem e hq
  · rintro y ⟨q, hq, hqy⟩
    change q ∈ connectedComponent (e p) at hq
    rw [← he] at hq
    rcases hq with ⟨z, hz, rfl⟩
    exact ⟨z, ⟨z, hz, rfl⟩, hqy⟩

end PoincareConjecture.AncientCompactness
