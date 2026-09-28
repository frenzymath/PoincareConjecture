import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTowerDescent
import PoincareConjecture.Proofs.M76.Wall.CutDiskProjection










set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)



def StageMarkedDisk.project
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
    {f : V2 → M} {r : M → ℝ} {C : Set M}
    {st : Stage e S f r C} {R Fmark : Set M}
    {base : Fmark} {J : Subgroup (FundamentalGroup Fmark base)}
    (disk : StageMarkedDisk st R Fmark base J)
    (hprojection : IsOpenEmbedding st.projection) :
    MarkedBoundaryPLLoopDisk e R Fmark base J where
  map := st.projection ∘ disk.map
  rim := disk.rim
  piecewiseAffine := disk.piecewiseAffine.project st.chartIndex st.projection.continuous
    st.chart_source (fun k x _ ↦ congrFun (st.chart_forward k) x)
  embedding := hprojection.isEmbedding.comp disk.embedding
  inside := disk.inside
  boundary_values := disk.boundary_values
  whole_boundary_iff := by
    intro x
    have h := disk.whole_boundary_iff x
    rwa [st.frontier_region R] at h
  basepath := disk.basepath
  outside := disk.outside

end Geometry.OriginalPLTower
