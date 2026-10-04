import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.ConeFields

/-!
# Actual general cone values and Cartesian fields

The coordinate-dependent calculation from M65 `InteriorRegularityConeDisk`
is generalized to a proper real Banach coordinate space. Its generic
AC composition, interpolation and polar transport lemmas are reused
from the independent authorized M65 closure. Source: Morrey ICM 1950,
pp. 183-185; M64 derivation `2026-09-26-general-half-cone.md`.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal InnerProductSpace

namespace PoincareMT.M64BoundaryCone

open M65Interior

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- The literal cone disk, with values in the reconstruction's actual target. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
def coneDiskMap {M : Type*} (P : C → M)
    (r : ℝ) (v0 : C)
    (v : ℝ → C) (x z : LoopPlane) : M :=
  P (coneCoordinates r v0 v (polarCoordinates x z).1 (polarCoordinates x z).2)

/-- The actual Cartesian field transported from the polar rectangle. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
def coneDiskField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : C → E) (r : ℝ)
    (v0 : C) (v d : ℝ → C)
    (x : LoopPlane) (i : Fin 2) (z : LoopPlane) : E :=
  coneCartesianField g r v0 v d (polarCoordinates x z).1 (polarCoordinates x z).2 i

/-- On the genuine angular chart the disk is the original literal polar cone. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
theorem coneDiskMap_polar {M : Type*} (P : C → M)
    (r : ℝ) (v0 : C)
    (v : ℝ → C) (x : LoopPlane) {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    coneDiskMap P r v0 v x (polarPlane x p) = P (coneCoordinates r v0 v p.1 p.2) := by
  simp only [coneDiskMap, polarCoordinates_polarPlane x hp]

/-- The genuine disk fields recover the actual rectangle fields on the angular chart. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
theorem coneDiskField_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : C → E) (r : ℝ)
    (v0 : C) (v d : ℝ → C)
    (x : LoopPlane) (i : Fin 2) {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    coneDiskField g r v0 v d x i (polarPlane x p) =
      coneCartesianField g r v0 v d p.1 p.2 i := by
  simp only [coneDiskField, polarCoordinates_polarPlane x hp]

end PoincareMT.M64BoundaryCone
