import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.OriginalPLStage

/-!
# Actual source rim points remain on the terminal frontier

The original local-homeomorphism projection retains the whole frontier.
A closed smaller region containing the source cannot make one of those
points interior. See Dehn derivation 010.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

variable {U E M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

/-- Every actual original rim point stays on the entire frontier of
the same closed relative neighborhood. No boundary nonemptiness is
asserted without such a point. See Dehn derivation 010. -/
theorem Stage.source_mem_frontier_of_original_rim (st : Stage e S f r C)
    {R : Set M} {N : Set st.Carrier} (hN : IsClosed N)
    (hDN : st.sourceMap '' S.space ⊆ N) (hNR : N ⊆ st.projection ⁻¹' R)
    {u : U} (hu : u ∈ S.space) (hfu : f u ∈ frontier R) :
    st.sourceMap u ∈ frontier N := by
  have hx : st.sourceMap u ∈ frontier (st.projection ⁻¹' R) := by
    rw [st.frontier_region]
    change st.projection (st.sourceMap u) ∈ frontier R
    rw [st.source_eq u hu]
    exact hfu
  rw [hN.frontier_eq]
  exact ⟨hDN (mem_image_of_mem st.sourceMap hu),
    fun hint => hx.2 (interior_mono hNR hint)⟩

end Geometry.OriginalPLTower
