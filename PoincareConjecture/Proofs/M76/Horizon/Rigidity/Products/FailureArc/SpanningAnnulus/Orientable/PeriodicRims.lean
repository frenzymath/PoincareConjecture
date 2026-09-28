import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.Orientable.FromPLTorus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.AnnularLift

set_option autoImplicit false
open Set Metric Geometry
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76
open PeriodicSquare Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem PLDomain.exists_original_spanning_pair_with_periodic_rims
    {X ι : Type} [TopologicalSpace X] [T2Space X]
    (O : LocalOrientation X)
    {e : ι → OpenPartialHomeomorph X V3} {R S₀ S₁ : Set X}
    (he : PLDomain e R) (hcompactR : IsCompact R) (hR : IsConnected R)
    (hS₀ : S₀ ⊆ frontier R) (hS₁ : S₁ ⊆ frontier R)
    (hdis : Disjoint S₀ S₁) (x₀ : S₀) (x₁ : S₁)
    (hcomponent₀ : connectedComponentIn (frontier R) (x₀ : X) = S₀)
    (hcomponent₁ : connectedComponentIn (frontier R) (x₁ : X) = S₁)
    (hinj : Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x₀))
    (k₀ : Path
      ((ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x₀)
      ((ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)) x₁))
    (hcomm : (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k₀.symm).toMonoidHom.comp
        (FundamentalGroup.map
          (ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)) x₁)).range))
    {p₀ p₁ : ℝ} [Fact (0 < p₀)] [Fact (0 < p₁)]
    (h₀ : (AddCircle p₀ × AddCircle p₀) ≃ₜ S₀)
    (h₁ : (AddCircle p₁ × AddCircle p₁) ≃ₜ S₁)
    (v₀ v₁ : ℝ × ℝ → X)
    (hv₀ : PolyhedralPLInCharts e v₀ (squareCarrier p₀))
    (hv₁ : PolyhedralPLInCharts e v₁ (squareCarrier p₁))
    (hvvalue₀ : ∀ z : Square p₀, v₀ (z.1, z.2) = (h₀ (projection p₀ z) : X))
    (hvvalue₁ : ∀ z : Square p₁, v₁ (z.1, z.2) = (h₁ (projection p₁ z) : X)) :
    ∃ (s₀ s₁ : Finset R)
      (K₀ : SimplicialComplex ℝ (s₀ → ℝ × V3))
      (K₁ : SimplicialComplex ℝ (s₁ → ℝ × V3))
      (F₀ : (s₀ → ℝ × V3) → X) (F₁ : (s₁ → ℝ × V3) → X)
      (H₀ : K₀.space ≃ₜ S₀) (H₁ : K₁.space ≃ₜ S₁)
      (M₀ : SourceSquareMap p₀ K₀) (M₁ : SourceSquareMap p₁ K₁)
      (g : Bool → V1 × V2 → X) (q : Bool → Q2 ≃ₜ AddCircle p₀)
      (r : Bool → ℝ → ℝ × ℝ),
      K₀.faces.Finite ∧ K₁.faces.Finite ∧
      PolyhedralPLInCharts e F₀ K₀.space ∧ PolyhedralPLInCharts e F₁ K₁.space ∧
      (∀ z : K₀.space, F₀ z = (H₀ z : X)) ∧
      (∀ z : K₁.space, F₁ z = (H₁ z : X)) ∧
      (∀ z : Square p₀, h₀ (projection p₀ z) = H₀ (M₀.map z)) ∧
      (∀ z : Square p₁, h₁ (projection p₁ z) = H₁ (M₁.map z)) ∧
      (∀ b, PolyhedralPLInCharts e (g b) source ∧
        InjOn (g b) source ∧ MapsTo (g b) source R ∧
        (∀ z ∈ source, g b z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1) ∧
        (∀ z : Q2, g b (endpoint false, z) =
          (h₀ (if b then (((p₀ / 2 : ℝ) : AddCircle p₀), q b z)
            else (q b z, ((p₀ / 2 : ℝ) : AddCircle p₀))) : X)) ∧
        ∀ z : Q2, g b (endpoint true, z) ∈ S₁) ∧
      ∀ b, FinitePiecewiseAffineOn (r b) (Icc (0 : ℝ) 1) ∧
        (∀ t : unitInterval, (h₁ (((r b t).1 : AddCircle p₁), ((r b t).2 : AddCircle p₁)) : X) =
          g b (endpoint true, Dehn.squareRimLoop t)) ∧
        (∀ s t : unitInterval,
          (((r b s).1 : AddCircle p₁), ((r b s).2 : AddCircle p₁)) =
            (((r b t).1 : AddCircle p₁), ((r b t).2 : AddCircle p₁)) ↔
          s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
        (fun t => (h₁ (((r b t).1 : AddCircle p₁), ((r b t).2 : AddCircle p₁)) : X)) '' Icc (0 : ℝ) 1 =
          (fun u => g b (endpoint true, u)) '' Q2 := by
  classical
  obtain ⟨_, s₀, _, K₀, F₀, H₀, M₀, g, q, _, _, hK₀, hF₀, hFval₀, _,
      hvalue₀, _, hg⟩ :=
    he.exists_original_coordinate_pair_of_PL_torus O hcompactR hR hS₀ hS₁ hdis
      x₀ x₁ hcomponent₀ hcomponent₁ hinj k₀ hcomm h₀ v₀ hv₀ hvvalue₀
  obtain ⟨_, s₁, _, K₁, F₁, H₁, M₁, _, _, hK₁, hF₁, hFval₁, _,
      hvalue₁, _⟩ :=
    he.exists_original_coordinates_of_PL_torus hcompactR hS₁ x₁ hcomponent₁
      h₁ v₁ hv₁ hvvalue₁
  have lifts (b : Bool) := M₁.exists_finitePL_annulus_rim_lift he.compatible H₁ F₁
    hF₁ hFval₁ h₁ hvalue₁ (g b) (hg b).1 (hg b).2.1 true (hg b).2.2.2.2.2
  choose r hr using lifts
  exact ⟨s₀, s₁, K₀, K₁, F₀, F₁, H₀, H₁, M₀, M₁, g, q, r, hK₀, hK₁,
    hF₀, hF₁, hFval₀, hFval₁, hvalue₀, hvalue₁, hg, hr⟩

end PoincareConjecture.M76
