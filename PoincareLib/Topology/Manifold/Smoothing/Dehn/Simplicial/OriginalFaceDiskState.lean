import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.SurfaceState
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalFaceMotionData
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Polyhedra.Mathlib.PolyhedralPLChartHomeomorph

/-!
# The actual proper disk retained at every finite face stage

The state records only the current original-atlas disk and its full
embedding, region, rim, mark and retained-neighborhood properties.
Applying an actually constructed face motion proves each property
for its literal endpoint composite. See Dehn032 finite-assembly
supplement, section4.
-/

set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

/-- An actual current disk on the fixed full source complex.
Initial data construct the first state; the actual face motion below
constructs every successor. No position assertion is a state field.
See Dehn032 finite-assembly supplement, section4. -/
abbrev FaceDiskState (t : Stage e S f r C) (K : SimplicialComplex ℝ V2)
    (U : K.faces → Set t.Carrier) (R Fmark : Set M) :=
  MarkedSurfaceState t K U R Fmark (Metric.sphere (0 : V2) 1)

/-- The next state is the literal composite with the actual ambient
endpoint. Each whole-source and whole-rim property follows from that
same motion, including original PL regularity and every retained
neighborhood. See Dehn032 finite-assembly supplement, section4. -/
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

/-- The complete source map, including values outside the source
carrier, is the actual endpoint composite. See Dehn032 finite-assembly
supplement, section4. -/
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
