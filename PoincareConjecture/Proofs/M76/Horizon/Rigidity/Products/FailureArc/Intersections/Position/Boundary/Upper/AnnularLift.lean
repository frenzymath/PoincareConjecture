import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.RimLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Coordinates.RimComponents
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.CylinderLift

set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76.PeriodicSquare
open Dehn Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1

theorem SourceSquareMap.exists_finitePL_annulus_rim_lift
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} {S : Set X}
    (M : SourceSquareMap p K) (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z))
    (f : V1 × V2 → X) (hf : PolyhedralPLInCharts e f source) (hfi : InjOn f source)
    (b : Bool) (hmark : ∀ u : Q, f (endpoint b, u) ∈ S) :
    ∃ r : ℝ → P2, FinitePiecewiseAffineOn r (Icc (0 : ℝ) 1) ∧
      (∀ t : unitInterval, (h (((r t).1 : AddCircle p), ((r t).2 : AddCircle p)) : X) =
        f (endpoint b, squareRimLoop t)) ∧
      (∀ s t : unitInterval,
        (((r s).1 : AddCircle p), ((r s).2 : AddCircle p)) =
          (((r t).1 : AddCircle p), ((r t).2 : AddCircle p)) ↔
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
      (fun t => (h (((r t).1 : AddCircle p), ((r t).2 : AddCircle p)) : X)) '' Icc (0 : ℝ) 1 =
        (fun u => f (endpoint b, u)) '' Q := by
  let A := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hA : A.faces.Finite :=
    squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hAs : A.space = Q :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  let l : V2 →ᴬ[ℝ] V1 × V2 :=
    (ContinuousAffineMap.const ℝ V2 (endpoint b)).prod (ContinuousAffineMap.id ℝ V2)
  have hl : MapsTo l Q source :=
    fun u hu => ⟨sphere_subset_closedBall (endpoint_mem_sphere b), hu⟩
  have hrim : PolyhedralPLInCharts e (fun u => f (endpoint b, u)) Q := by
    rw [← hAs]
    exact hf.comp_finitePiecewiseAffineOn A hA
      ((A.affineOnFaces_affine l).finitePiecewiseAffineOn hA)
      (fun u hu => hl (hAs.subset hu))
  have hrimi : InjOn (fun u => f (endpoint b, u)) Q := by
    intro u hu v hv heq
    exact congrArg Prod.snd (hfi (hl hu) (hl hv) heq)
  exact M.exists_finitePL_embedded_rim_lift hcompat H F hF hFval h hvalue
    (fun u => f (endpoint b, u)) hrim (fun u hu => hmark ⟨u, hu⟩) hrimi

end PoincareConjecture.M76.PeriodicSquare
