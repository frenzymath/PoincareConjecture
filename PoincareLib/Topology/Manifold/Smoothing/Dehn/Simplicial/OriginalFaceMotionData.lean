import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.FaceData
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.OriginalPLSuccessor
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Isotopy.Mathlib.PLCarrierMotion

/-!
# The actual geometric data retained at one original face step

Package the polyhedra, coordinate motion and original ambient family
constructed by the two original phase producers. The finite history
keeps these particular witnesses at every index. No record-producing
supplier is assumed by the actual assembly theorem.
See Hudson1969, Lemma4.6, Dehn032, sections4--6, and its reviewed
finite-assembly data supplement, sections1--4.
-/

set_option autoImplicit false

open Set Geometry unitInterval

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

/-- Actual output of one original boundary/interior face motion.
The literal current map, old prefix, successor, unchanged Step,
paired charts and retained open neighborhoods index all fields.
The two concrete phase producers construct this record; it is not
an additional geometric input. See Dehn032 finite-assembly supplement,
sections1--4. -/
abbrev FaceMotionData {s t : Stage e S f r C} (step : Step s t)
    (K K₀ K₁ : SimplicialComplex ℝ V2) (j : V2 → t.Carrier)
    (Q : OpenPartialHomeomorph t.Carrier V3)
    (B : OpenPartialHomeomorph s.Carrier V3) (J : SimplicialComplex ℝ V3)
    (U : K.faces → Set t.Carrier) (R Fmark : Set M) (boundary : Bool) :=
  MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary

end Geometry.OriginalPLTower
