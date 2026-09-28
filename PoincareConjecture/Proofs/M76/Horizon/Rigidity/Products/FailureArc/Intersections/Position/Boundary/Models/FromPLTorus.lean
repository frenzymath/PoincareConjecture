import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.Component
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusSquareMap
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.BoundaryLocalConnectedness



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
open PeriodicSquare

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_original_coordinates_of_PL_torus
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hS : S ⊆ frontier R) (x : S)
    (hcomponent : connectedComponentIn (frontier R) (x : X) = S)
    {p : ℝ} [Fact (0 < p)] (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (v : ℝ × ℝ → X) (hv : PolyhedralPLInCharts e v (squareCarrier p))
    (hvvalue : ∀ z : Square p, v (z.1, z.2) = (h (projection p z) : X)) :
    IsClopen ((Subtype.val : frontier R → X) ⁻¹' S) ∧
    ∃ (s : Finset R) (phi : X → (s → ℝ × V3))
      (J : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X)
      (H : J.space ≃ₜ S) (M : SourceSquareMap p J),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      J.faces.Finite ∧ PolyhedralPLInCharts e g J.space ∧
      (∀ z : J.space, g z = (H z : X)) ∧
      (∀ z ∈ J.space, phi (g z) = z) ∧
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
      FinitePiecewiseAffineOn (phi ∘ v) (squareCarrier p) := by
  have hp : 0 < p := Fact.out
  obtain ⟨s, phi, J, g, H, hphi, hphiPL, hJ, _, _, _, _, hg, hgvalue, hinverse⟩ :=
    he.exists_original_component_model hR hS x hcomponent
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc hp).prod (isFinitePLBallPair_Icc hp)
  have hvL : PolyhedralPLInCharts e v L.space := by
    rw [hLs]
    exact hv
  have hu : FinitePiecewiseAffineOn (phi ∘ v) (squareCarrier p) := by
    change FinitePiecewiseAffineOn (phi ∘ v) (Icc 0 p ×ˢ Icc 0 p)
    exact hLs ▸ hvL.finitePiecewiseAffineOn_comp L hL hphiPL
  let k := h.trans H.symm
  have huvalue (z : Square p) : (phi ∘ v) (z.1, z.2) = (k (projection p z) : s → ℝ × V3) := by
    change phi (v (z.1, z.2)) = (H.symm (h (projection p z)) : s → ℝ × V3)
    rw [hvvalue]
    have hgpoint := hgvalue (H.symm (h (projection p z)))
    rw [H.apply_symm_apply] at hgpoint
    rw [← hgpoint]
    exact hinverse _ (H.symm (h (projection p z))).property
  let M := SourceSquareMap.of_torusHomeomorph (p := p) k (phi ∘ v) hu huvalue
  refine ⟨he.isClopen_preimage_frontier_component hR (hS x.property) hcomponent,
    s, phi, J, g, H, M, hphi, hphiPL, hJ, hg, hgvalue, hinverse, ?_, hu⟩
  intro z
  change h (projection p z) = H (H.symm (h (projection p z)))
  exact (H.apply_symm_apply _).symm

end PoincareConjecture.M76
