import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.OriginalParameter
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.OriginalModel

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
open PeriodicSquare

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

theorem PLDomain.exists_original_retained_PL_torus
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R S : Set X0}
    (he : PLDomain e R) (hR : IsCompact R) (hS : S ⊆ frontier R) (x : S)
    (hcomponent : connectedComponentIn (frontier R) (x : X0) = S)
    (hnt : Nontrivial (FundamentalGroup S x))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X0)) x)) :
    ∃ (h : (AddCircle (64 : ℝ) × AddCircle (64 : ℝ)) ≃ₜ S) (v : ℝ × ℝ → X0),
      PolyhedralPLInCharts e v (squareCarrier 64) ∧
      ∀ z : Square 64, v (z.1, z.2) = (h (projection 64 z) : X0) := by
  let : Fact (0 < (64 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨_, s, K, F, H, M, h, _, hF, hFval, hvalue⟩ :=
    he.exists_original_boundary_torus_coordinates hR hS x hcomponent hnt hinj
  obtain ⟨v, hv, hval⟩ := M.exists_original_PL_parameter H F hF hFval h hvalue
  exact ⟨h, v, hv, hval⟩

end PoincareConjecture.M76
