import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Recognition.OriginalFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.BoundaryLocalConnectedness

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
open PeriodicSquare
local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

theorem PLDomain.exists_original_boundary_torus_coordinates
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R S : Set X0}
    (he : PLDomain e R) (hR : IsCompact R) (hS : S ⊆ frontier R) (x : S)
    (hcomponent : connectedComponentIn (frontier R) (x : X0) = S)
    (hnt : Nontrivial (FundamentalGroup S x))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X0)) x)) :
    IsClopen ((Subtype.val : frontier R → X0) ⁻¹' S) ∧
    ∃ (s : Finset R) (K : SimplicialComplex ℝ (s → ℝ × V3))
      (F : (s → ℝ × V3) → X0) (H : K.space ≃ₜ S)
      (model : SourceSquareMap 64 K) (h : (AddCircle (64 : ℝ) × AddCircle (64 : ℝ)) ≃ₜ S),
      K.faces.Finite ∧ PolyhedralPLInCharts e F K.space ∧
      (∀ z : K.space, F z = (H z : X0)) ∧
      ∀ z : Square 64, h (projection 64 z) = H (model.map z) := by
  rcases x with ⟨x, hxS⟩
  change connectedComponentIn (frontier R) x = S at hcomponent
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let : Fact (0 < (64 : ℝ)) := ⟨by norm_num⟩
  have hx : x ∈ frontier R := hS hxS
  have hnt' : Nontrivial (FundamentalGroup (connectedComponentIn (frontier R) (x : X0))
      ⟨x, mem_connectedComponentIn hx⟩) := by
    subst S
    exact hnt
  have hinj' : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(connectedComponentIn (frontier R) (x : X0), X0)) ⟨x, mem_connectedComponentIn hx⟩) := by
    subst S
    exact hinj
  obtain ⟨s, _, K, F, H, _, _, hK, hF, hFval, _, ⟨model⟩⟩ :=
    he.exists_original_frontier_torus_square_model e he.cover he.compatible hR x hx hnt' hinj'
  obtain ⟨h, hvalue⟩ := exists_homeomorph_of_sourceSquareMap 64 model
  let H' := H.trans (Homeomorph.setCongr hcomponent)
  refine ⟨he.isClopen_preimage_frontier_component hR hx hcomponent,
    s, K, F, H', model, h.trans H', hK, hF, fun z => (hFval z).symm, ?_⟩
  intro z
  change H' (h (projection 64 z)) = H' (model.map z)
  rw [hvalue]

end PoincareConjecture.M76
