import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Topology.CompactPLNeighborhoodModel
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.AtlasOfCover
import Mathlib.Topology.Metrizable.Basic

/-!
# An actual metrizable open neighborhood of a compact PL core

The existing finite graph model embeds the interior of its compact
neighborhood in a finite-dimensional normed space. The induced metric
is compatible with the original subtype topology; no metric on the
whole ambient space is assumed. See Wall derivation006, section1.
-/

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

/-- Every compact set in the original PL atlas has a metrizable open
neighborhood inside its prescribed open region. The metric topology
is the unchanged original subtype topology. See Wall006, section1. -/
theorem exists_metrizable_open_neighborhood
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X E)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    {A W : Set X} (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ N : Set X, IsOpen N ∧ A ⊆ N ∧ N ⊆ W ∧
      TopologicalSpace.MetrizableSpace N := by
  let := ChartedSpace.ofChartCover e hcover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  obtain ⟨s, _, C, J, H, _, hAC, hCW, _, _, _, _, _⟩ :=
    exists_compact_PL_neighborhood_model e hcompat hcover hA hW hAW
  have hH : Topology.IsEmbedding (fun x : C => (H x : s → ℝ × E)) :=
    Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  have hm := hH.comp
    (Topology.IsEmbedding.inclusion (interior_subset : interior C ⊆ C))
  exact ⟨interior C, isOpen_interior, hAC, interior_subset.trans hCW,
    hm.metrizableSpace⟩

end OpenPartialHomeomorph
