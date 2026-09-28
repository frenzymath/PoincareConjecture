import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Strips.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Source.CopiedFibers

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem interval_strips_stay_in_marked_copies
    {S T : Set P2} (hS : IsClosed S) (hT : IsClosed T) (hdis : Disjoint S T)
    (c : Bool → P2 → P2)
    (hc : ∀ j, ContinuousOn (c j) source)
    (hsub : ∀ j, MapsTo (c j) source (S ∪ T))
    (hzero₀ : c false (0,0) ∈ S) (hzero₁ : c true (0,0) ∈ T) :
    MapsTo (c false) source S ∧ MapsTo (c true) source T := by
  have hsrc : IsConnected source :=
    (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).prod
      (isConnected_Icc (by norm_num : (-1 : ℝ) ≤ 1))
  have hzero : ((0,0) : P2) ∈ source := by
    constructor <;> norm_num
  have hcases (j : Bool) : c j '' source ⊆ S ∨ c j '' source ⊆ T :=
    isPreconnected_iff_subset_of_disjoint_closed.mp
      (hsrc.image (c j) (hc j)).isPreconnected S T hS hT
      (image_subset_iff.mpr (hsub j)) (by rw [hdis.inter_eq,inter_empty])
  constructor
  · exact image_subset_iff.mp ((hcases false).resolve_right
      (fun h => disjoint_left.mp hdis hzero₀ (h ⟨(0,0),hzero,rfl⟩)))
  · exact image_subset_iff.mp ((hcases true).resolve_left
      (fun h => disjoint_left.mp hdis (h ⟨(0,0),hzero,rfl⟩) hzero₁))

end PoincareConjecture.M76.Dehn.Annuli
