import PoincareConjecture.Proofs.M76.Dehn.OriginalPLStage









set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

variable {U E M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}




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
