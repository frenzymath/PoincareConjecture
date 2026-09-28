import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.FromPLTorus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.Orientable.CoordinatePair
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.CollarKernelInjectivity








set_option autoImplicit false
open Set Metric Geometry
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76
open PeriodicSquare Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem PLDomain.exists_original_coordinate_pair_of_PL_torus
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
    {p : ℝ} [Fact (0 < p)] (h : (AddCircle p × AddCircle p) ≃ₜ S₀)
    (v : ℝ × ℝ → X) (hv : PolyhedralPLInCharts e v (squareCarrier p))
    (hvvalue : ∀ z : Square p, v (z.1, z.2) = (h (projection p z) : X)) :
    IsClopen ((Subtype.val : frontier R → X) ⁻¹' S₀) ∧
    ∃ (s : Finset R) (phi : X → (s → ℝ × V3))
      (K : SimplicialComplex ℝ (s → ℝ × V3)) (F : (s → ℝ × V3) → X)
      (H : K.space ≃ₜ S₀) (M : SourceSquareMap p K)
      (g : Bool → V1 × V2 → X) (q : Bool → Q2 ≃ₜ AddCircle p),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧ PolyhedralPLInCharts e F K.space ∧
      (∀ z : K.space, F z = (H z : X)) ∧
      (∀ z ∈ K.space, phi (F z) = z) ∧
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
      FinitePiecewiseAffineOn (phi ∘ v) (squareCarrier p) ∧
      (∀ b, PolyhedralPLInCharts e (g b) source ∧
        InjOn (g b) source ∧ MapsTo (g b) source R ∧
        (∀ z ∈ source, g b z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1) ∧
        (∀ z : Q2, g b (endpoint false, z) =
          (h (if b then (((p / 2 : ℝ) : AddCircle p), q b z)
            else (q b z, ((p / 2 : ℝ) : AddCircle p))) : X)) ∧
        ∀ z : Q2, g b (endpoint true, z) ∈ S₁) := by
  classical
  obtain ⟨hclopen, s, phi, K, F, H, M, hphi, hphiPL, hK, hF, hFval, hinverse,
      hvalue, hvPL⟩ :=
    he.exists_original_coordinates_of_PL_torus hcompactR hS₀ x₀ hcomponent₀ h v hv hvvalue
  letI : PathConnectedSpace S₀ := h.surjective.pathConnectedSpace h.continuous
  have hinjAll (x : S₀) : Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x) :=
    Poincare.Topology.fundamentalGroup_map_injective_of_path
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset))
      (PathConnectedSpace.somePath x x₀) hinj
  obtain ⟨h', g, q, hvalue', hg⟩ :=
    M.exists_original_coordinate_pair_of_localOrientation O he hcompactR hR hS₀ hS₁
      hdis x₀ x₁ hcomponent₀ hcomponent₁ hinjAll k₀ hcomm H F hF hFval
  have hh : h' = h := by
    apply Homeomorph.ext
    intro z
    obtain ⟨w, rfl⟩ := surjective_projection p z
    exact (hvalue' w).trans (hvalue w).symm
  subst h'
  exact ⟨hclopen, s, phi, K, F, H, M, g, q, hphi, hphiPL, hK, hF, hFval,
    hinverse, hvalue, hvPL, hg⟩

end PoincareConjecture.M76
