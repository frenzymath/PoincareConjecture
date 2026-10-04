import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.Regions.Regions
import PoincareLib.Topology.Manifold.Schoenflies.Plane.Polygon.Regions.LocalRegionSides
open Poincare.Manifold.Schoenflies.Plane

/-!
# Opposite local rays lie in opposite polygon regions

The local labeling step for the inside arcs in Munkres (1960),
Lemma 2.4, pp. 195-196. Frontier contact supplies an actual exterior
witness, so neither given local side needs a preassigned region label.
See `smale/derivations/2026-09-23-open-arc-inside-matching.md`, stage 2.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {m : ℕ} {r : Polygon E m}

/-- Entire short rays on opposite preconnected local sides have opposite
canonical region labels; Munkres, Lemma 2.4, pp. 195-196. -/
theorem IsSimplePolygon.opposite_local_rays_regions (hr : IsSimplePolygon r)
    (hdim : Module.finrank ℝ E = 2) (q a b : E) (ε : ℝ) (W A B : Set E)
    (hq : q ∈ r.boundary ℝ) (_hε : 0 < ε) (hW : IsOpen W) (hqW : q ∈ W)
    (hA : IsPreconnected A) (hB : IsPreconnected B) (hlocal : A ∪ B = W \ r.boundary ℝ)
    (hqa : ∀ t ∈ Ioo 0 ε, AffineMap.lineMap q a t ∈ A)
    (hqb : ∀ t ∈ Ioo 0 ε, AffineMap.lineMap q b t ∈ B) :
    ((∀ t ∈ Ioo 0 ε, AffineMap.lineMap q a t ∈ polygonInterior r) ∧
      (∀ t ∈ Ioo 0 ε, AffineMap.lineMap q b t ∈ polygonExterior r)) ∨
    ((∀ t ∈ Ioo 0 ε, AffineMap.lineMap q a t ∈ polygonExterior r) ∧
      (∀ t ∈ Ioo 0 ε, AffineMap.lineMap q b t ∈ polygonInterior r)) := by
  obtain ⟨hI, hO, _, _, hdis, hcover, _, _, hIf, hOf⟩ := hr.polygonRegions_spec hdim
  have hqOf : q ∈ frontier (polygonExterior r) := hOf.symm ▸ hq
  obtain ⟨y, hyW, hyO⟩ := mem_closure_iff.mp (frontier_subset_closure hqOf) W hW hqW
  have hyAB : y ∈ A ∪ B :=
    hlocal.symm ▸ (show y ∈ W \ r.boundary ℝ from ⟨hyW, hyO.1⟩)
  rcases hyAB with hyA | hyB
  · obtain ⟨hBI, hAO⟩ := preconnected_local_sides_subset_regions hI hO hdis hcover
      hW hqW (hIf.symm ▸ hq) hB hA ((union_comm B A).trans hlocal) ⟨y, hyA, hyO⟩
    exact Or.inr ⟨fun t ht => hAO (hqa t ht), fun t ht => hBI (hqb t ht)⟩
  · obtain ⟨hAI, hBO⟩ := preconnected_local_sides_subset_regions hI hO hdis hcover
      hW hqW (hIf.symm ▸ hq) hA hB hlocal ⟨y, hyB, hyO⟩
    exact Or.inl ⟨fun t ht => hAI (hqa t ht), fun t ht => hBO (hqb t ht)⟩

end PoincareMT.M25.Topology3D
