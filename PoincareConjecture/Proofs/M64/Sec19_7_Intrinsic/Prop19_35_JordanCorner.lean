import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanRegion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.TwoRaySupport
import Mathlib.Topology.OpenPartialHomeomorph.IsImage













noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture





theorem m64Intrinsic_jordan_interior_closure
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfront : frontier U = frontier V) :
    interior (closure U) = U ∧ frontier (closure U) = frontier U := by
  have hiV : Disjoint (interior (closure U)) (closure V) :=
    ((hdisj.closure_left hV).mono_left interior_subset).closure_right isOpen_interior
  have hi : interior (closure U) = U := by
    apply Subset.antisymm _ hU.subset_interior_closure
    intro p hp
    by_contra hn
    have hpfront : p ∈ frontier U := ⟨interior_subset hp, by simpa [hU.interior_eq] using hn⟩
    rw [hfront] at hpfront
    exact disjoint_left.mp hiV hp hpfront.1
  refine ⟨hi, ?_⟩
  rw [frontier, closure_closure, hi, frontier, hU.interior_eq]






theorem m64Intrinsic_jordan_corner_germ
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfront : frontier U = frontier V)
    (H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (c : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hc : c 0 ∈ H.source) (hp : H (c 0) ∈ frontier U)
    (hrays : ∀ᶠ z in 𝓝 (c 0), H z ∈ frontier U ↔
      (c.coord 1 z = 0 ∧ 0 ≤ c.coord 2 z) ∨
        (0 ≤ c.coord 1 z ∧ c.coord 2 z = 0)) :
    (∀ᶠ z in 𝓝 (c 0), H z ∈ closure U ↔
      0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z) ∨
    (∀ᶠ z in 𝓝 (c 0), H z ∈ closure U ↔
      c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0) := by
  let S := H.source ∩ H ⁻¹' U
  let K := closure S
  have hS : IsOpen S := H.isOpen_inter_preimage hU
  have himage : H.IsImage S U := by
    intro z hz
    exact ⟨fun hu => ⟨hz, hu⟩, fun hu => hu.2⟩
  have hregular : closure (interior K) = K := by
    apply Subset.antisymm isClosed_closure.closure_interior_subset
    exact closure_mono hS.subset_interior_closure
  have hfcl := (m64Intrinsic_jordan_interior_closure hU hV hdisj hfront).2
  have hKfront : c 0 ∈ frontier K := by
    apply (himage.closure.frontier hc).mp
    rwa [hfcl]
  have hraysK : frontier K =ᶠ[𝓝 (c 0)]
      {z | (c.coord 1 z = 0 ∧ 0 ≤ c.coord 2 z) ∨
        (0 ≤ c.coord 1 z ∧ c.coord 2 z = 0)} := by
    filter_upwards [H.open_source.mem_nhds hc, hrays] with z hz hr
    apply propext
    change z ∈ frontier K ↔
      (c.coord 1 z = 0 ∧ 0 ≤ c.coord 2 z) ∨
        (0 ≤ c.coord 1 z ∧ c.coord 2 z = 0)
    rw [← himage.closure.frontier hz, hfcl]
    exact hr
  rcases Topology.Surface.closed_regular_support_germ_of_two_rays c
    isClosed_closure hregular hKfront hraysK with h | h
  · left
    filter_upwards [H.open_source.mem_nhds hc, h] with z hz heq
    exact (himage.closure hz).trans (propext_iff.mp heq)
  · right
    filter_upwards [H.open_source.mem_nhds hc, h] with z hz heq
    exact (himage.closure hz).trans (propext_iff.mp heq)





theorem m64Intrinsic_jordan_positive_corner_germ
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfront : frontier U = frontier V)
    (H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (c : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hc : c 0 ∈ H.source) (hp : H (c 0) ∈ frontier U)
    (hrays : ∀ᶠ z in 𝓝 (c 0), H z ∈ frontier U ↔
      (c.coord 1 z = 0 ∧ 0 ≤ c.coord 2 z) ∨
        (0 ≤ c.coord 1 z ∧ c.coord 2 z = 0))
    (hoccupied : ∃ᶠ z in 𝓝 (c 0),
      0 < c.coord 1 z ∧ 0 < c.coord 2 z ∧ H z ∈ U) :
    ∀ᶠ z in 𝓝 (c 0), H z ∈ closure U ↔
      0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z := by
  rcases m64Intrinsic_jordan_corner_germ hU hV hdisj hfront H c hc hp hrays with h | h
  · exact h
  · obtain ⟨z, hz, hside⟩ := (hoccupied.and_eventually h).exists
    rcases hside.mp (subset_closure hz.2.2) with hn | hn
    · exact False.elim (not_lt_of_ge hn hz.1)
    · exact False.elim (not_lt_of_ge hn hz.2.1)

end PoincareConjecture
