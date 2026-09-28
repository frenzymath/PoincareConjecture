import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.ProtectedRegion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.MarkedRims

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)

theorem original_terminal_rim_graphs (d : ProtectedAnnulusTerminalData L retained)
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source) :
    let g := fun b ↦ d.compact_region.graph ∘ d.stage.annulusRimMap b
    (∀ b, FinitePiecewiseAffineOn (g b) Q2) ∧
    (∀ b, InjOn (g b) Q2) ∧
    (∀ b, MapsTo (g b) Q2 d.compact_region.boundary.space) ∧
    Disjoint (g false '' Q2) (g true '' Q2) := by
  classical
  let N := d.compact_region
  let F := N.graph
  let rim := d.stage.annulusRim d.source_space
  let J := N.homeomorph
  have hrimN (b : Bool) (u : Q2) : rim b u ∈ N.region :=
    N.source_subset (d.stage.annulusRim_range_subset d.source_space b (mem_range_self u))
  have hrimI (b : Bool) : Function.Injective (rim b) :=
    (d.stage.annulusRim_isClosedEmbedding d.source_space b
      (prescribed_rim_injective L retained hsource d.boundary_values b)).injective
  have hrimD : Disjoint (range (rim false)) (range (rim true)) :=
    d.stage.annulusRim_ranges_disjoint d.source_space
      (prescribed_rim_ranges_disjoint L retained hsource d.boundary_values)
  have hFeq (b c : Bool) (u v : Q2) (heq : F (rim b u) = F (rim c v)) :
      rim b u = rim c v := by
    have hh : J ⟨rim b u, hrimN b u⟩ = J ⟨rim c v, hrimN c v⟩ := by
      apply Subtype.ext
      rw [N.homeomorph_value, N.homeomorph_value]
      exact heq
    exact congrArg Subtype.val (J.injective hh)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    let K := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
    have hK := squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
    have hKs : K.space = Q2 :=
      (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
        boundary_squareRimPolygon
    have hPL := d.stage.annulusRim_polyhedral d.source_space b
    rw [← hKs] at hPL
    simpa only [hKs] using hPL.finitePiecewiseAffineOn_comp K hK N.graph_PL
  · intro b u hu v hv huv
    exact congrArg Subtype.val (hrimI b (hFeq b b ⟨u, hu⟩ ⟨v, hv⟩ huv))
  · intro b u hu
    rw [N.boundary_image]
    refine ⟨rim b ⟨u, hu⟩, ?_, rfl⟩
    apply N.source_frontier (ProtectedAnnulus.endpoint b, u)
      (d.source_space.symm.subset ⟨sphere_subset_closedBall (endpoint_mem_sphere b), hu⟩)
    exact (d.frontier_iff ⟨(ProtectedAnnulus.endpoint b, u),
      sphere_subset_closedBall (endpoint_mem_sphere b), hu⟩).mpr (endpoint_mem_sphere b)
  · apply disjoint_left.mpr
    rintro z ⟨u, hu, huz⟩ ⟨v, hv, hvz⟩
    have heq := hFeq false true ⟨u, hu⟩ ⟨v, hv⟩ (huz.trans hvz.symm)
    exact disjoint_left.mp hrimD (mem_range_self ⟨u, hu⟩) ⟨⟨v, hv⟩, heq.symm⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
