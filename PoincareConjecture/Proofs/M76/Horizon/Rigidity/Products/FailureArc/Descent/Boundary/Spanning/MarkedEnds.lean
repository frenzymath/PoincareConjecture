import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.ResolutionEndHomotopies
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem tube_end_mapsTo_original_mark
    {X : Type*} [TopologicalSpace X] {R W : Set X}
    (mark : Bool → Set X)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → X) ⁻¹' mark b))
    (hdis : Disjoint (mark false) (mark true))
    (τ : C3 → X) (hτ : ContinuousOn τ tube) (hW : MapsTo τ tube W)
    (htrace : W ∩ frontier R ⊆ mark false ∪ mark true)
    (hfront : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (b : Bool) (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1)
    (hcenter : τ ((0, 0), t) ∈ mark b) :
    ∀ z ∈ tube, z.2 = t → τ z ∈ mark b := by
  have hKt : endSquare t ⊆ tube := fun z hz ↦ ⟨hz.1, hz.2.symm ▸ t.property⟩
  have hKfront (z : endSquare t) : τ z ∈ frontier R :=
    (hfront z (hKt z.property)).mpr (z.property.2.symm ▸ ht)
  let p : C(endSquare t, frontier R) :=
    ⟨fun z ↦ ⟨τ z, hKfront z⟩,
      ((hτ.mono hKt).domRestrict).subtype_mk _⟩
  let F (i : Bool) : Set (endSquare t) := p ⁻¹' ((Subtype.val : frontier R → X) ⁻¹' mark i)
  have hFopen (i : Bool) : IsOpen (F i) := (hopen i).preimage p.continuous
  have hFd : Disjoint (F false) (F true) := by
    refine disjoint_left.mpr ?_
    intro z h0 h1
    exact disjoint_left.mp hdis h0 h1
  have hFc : (univ : Set (endSquare t)) ⊆ F false ∪ F true :=
    fun z _ ↦ htrace ⟨hW (hKt z.property), hKfront z⟩
  let : PreconnectedSpace (endSquare t) := isPreconnected_iff_preconnectedSpace.mp
    ((((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)).prod
      (convex_singleton (t : ℝ))).isPreconnected)
  have hside : (univ : Set (endSquare t)) ⊆ F b := by
    have hstart : (endCenter t : endSquare t) ∈ F b := hcenter
    rcases isPreconnected_univ.subset_or_subset (hFopen false) (hFopen true) hFd hFc with h | h
    · cases b
      · exact h
      · exact (disjoint_left.mp hFd (h (mem_univ _)) hstart).elim
    · cases b
      · exact (disjoint_left.mp hFd hstart (h (mem_univ _))).elim
      · exact h
  intro z hz he
  exact hside (a := ⟨z, hz.1, he⟩) (mem_univ _)

end PoincareConjecture.M76.Dehn
