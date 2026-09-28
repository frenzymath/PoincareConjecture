import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Restriction

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem isConnected_openTube {r : ℝ} (hr : 0 < r) : IsConnected (openTube r) := by
  have h := ((isConnected_Ioo (show -r < r by linarith)).prod
    (isConnected_Ioo (show -r < r by linarith))).prod
    (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1))
  simpa only [openTube,transverseSquare,interior_prod_eq,interior_Icc] using h

theorem origin_mem_openTube {r : ℝ} (hr : 0 < r) : ((0,0),0) ∈ openTube r := by
  simp only [openTube,transverseSquare,interior_prod_eq,interior_Icc,mem_prod,mem_Ioo,mem_Icc]
  exact ⟨⟨⟨by linarith,hr⟩,⟨by linarith,hr⟩⟩,le_rfl,zero_le_one⟩

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem OriginalIntervalTube.isConnected_openTube_image
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    IsConnected (U.map '' openTube r) :=
  (isConnected_openTube hr).image U.map
    (U.pl.continuousOn.mono ((openTube_subset r).trans (closedTube_subset hr1)))

theorem OriginalIntervalTube.openTube_meets_frontier
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ((U.map '' openTube r) ∩ frontier R).Nonempty := by
  have h0 := origin_mem_openTube hr
  exact ⟨U.map ((0,0),0),⟨((0,0),0),h0,rfl⟩,
    (U.frontier_iff _ (closedTube_subset hr1 (openTube_subset r h0))).mpr (Or.inl rfl)⟩

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
