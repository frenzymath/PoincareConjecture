import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.FaceData
import PoincareConjecture.Proofs.M76.Dehn.OriginalPLSuccessor
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMotion












set_option autoImplicit false

open Set Geometry unitInterval

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}







abbrev FaceMotionData {s t : Stage e S f r C} (step : Step s t)
    (K K₀ K₁ : SimplicialComplex ℝ V2) (j : V2 → t.Carrier)
    (Q : OpenPartialHomeomorph t.Carrier V3)
    (B : OpenPartialHomeomorph s.Carrier V3) (J : SimplicialComplex ℝ V3)
    (U : K.faces → Set t.Carrier) (R Fmark : Set M) (boundary : Bool) :=
  MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary

end Geometry.OriginalPLTower
