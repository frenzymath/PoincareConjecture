import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.FaceData
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLChartHomeomorph











set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}





structure MarkedSurfaceState (t : Stage e S f r C) (K : SimplicialComplex ℝ V)
    (U : K.faces → Set t.Carrier) (R Fmark : Set M) (rimSet : Set V) where
  map : V → t.Carrier
  original_PL : PolyhedralPLInCharts t.charts map K.space
  embedding : IsEmbedding (fun x : K.space => map x)
  region : MapsTo map K.space (t.projection ⁻¹' R)
  proper : ∀ x ∈ K.space,
    map x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ rimSet
  mark : MapsTo map (rimSet) (t.projection ⁻¹' Fmark)
  retained : ∀ a : K.faces, MapsTo map (convexHull ℝ (a.val : Set V)) (U a)





def MarkedSurfaceState.move {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} (hK : K.faces.Finite)
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {rimSet : Set V}
    (state : MarkedSurfaceState t K U R Fmark rimSet)
    {Q : OpenPartialHomeomorph t.Carrier E}
    {B : OpenPartialHomeomorph s.Carrier E} {J : SimplicialComplex ℝ E}
    {boundary : Bool}
    (motion : MarkedSurfaceMotionData step K K₀ K₁ state.map Q B J U R Fmark boundary) :
    MarkedSurfaceState t K U R Fmark rimSet where
  map := motion.ambient 1 ∘ state.map
  original_PL := state.original_PL.comp_chart_homeomorph K hK (motion.ambient 1)
    t.cover (motion.original_PL 1)
  embedding := (motion.ambient 1).isEmbedding.comp state.embedding
  region := by
    intro x hx
    change state.map x ∈ (motion.ambient 1) ⁻¹' (t.projection ⁻¹' R)
    rw [motion.region]
    exact state.region hx
  proper := by
    intro x hx
    have hfront : (motion.ambient 1) ⁻¹' frontier (t.projection ⁻¹' R) =
        frontier (t.projection ⁻¹' R) := by
      rw [(motion.ambient 1).preimage_frontier, motion.region]
    exact (Set.ext_iff.mp hfront (state.map x)).trans (state.proper x hx)
  mark := by
    intro x hx
    change state.map x ∈ (motion.ambient 1) ⁻¹' (t.projection ⁻¹' Fmark)
    rw [motion.mark]
    exact state.mark hx
  retained := motion.retained 1




theorem MarkedSurfaceState.move_map {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} (hK : K.faces.Finite)
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {rimSet : Set V}
    (state : MarkedSurfaceState t K U R Fmark rimSet)
    {Q : OpenPartialHomeomorph t.Carrier E}
    {B : OpenPartialHomeomorph s.Carrier E} {J : SimplicialComplex ℝ E}
    {boundary : Bool}
    (motion : MarkedSurfaceMotionData step K K₀ K₁ state.map Q B J U R Fmark boundary) :
    (state.move hK motion).map = motion.ambient 1 ∘ state.map := rfl

end Geometry.OriginalPLTower
