import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.SurfaceState
import PoincareConjecture.Proofs.M76.Dehn.OriginalFaceMotionData
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLChartHomeomorph











set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}





abbrev FaceDiskState (t : Stage e S f r C) (K : SimplicialComplex ℝ V2)
    (U : K.faces → Set t.Carrier) (R Fmark : Set M) :=
  MarkedSurfaceState t K U R Fmark (Metric.sphere (0 : V2) 1)





noncomputable def FaceDiskState.move {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} (hK : K.faces.Finite)
    {U : K.faces → Set t.Carrier} {R Fmark : Set M}
    (state : FaceDiskState t K U R Fmark)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ state.map Q B J U R Fmark boundary) :
    FaceDiskState t K U R Fmark :=
  MarkedSurfaceState.move hK state motion




theorem FaceDiskState.move_map {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} (hK : K.faces.Finite)
    {U : K.faces → Set t.Carrier} {R Fmark : Set M}
    (state : FaceDiskState t K U R Fmark)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ state.map Q B J U R Fmark boundary) :
    (state.move hK motion).map = motion.ambient 1 ∘ state.map := rfl

end Geometry.OriginalPLTower
