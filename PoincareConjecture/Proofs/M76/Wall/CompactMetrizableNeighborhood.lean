import PoincareConjecture.Proofs.M76.Mathlib.CompactPLNeighborhoodModel
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover
import Mathlib.Topology.Metrizable.Basic

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

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
