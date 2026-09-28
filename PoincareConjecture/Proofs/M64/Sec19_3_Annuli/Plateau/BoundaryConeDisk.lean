import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeFields














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal InnerProductSpace

namespace PoincareConjecture.M64BoundaryCone

open M65Interior

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]




def coneDiskMap {M : Type*} (P : C → M)
    (r : ℝ) (v0 : C)
    (v : ℝ → C) (x z : LoopPlane) : M :=
  P (coneCoordinates r v0 v (polarCoordinates x z).1 (polarCoordinates x z).2)




def coneDiskField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : C → E) (r : ℝ)
    (v0 : C) (v d : ℝ → C)
    (x : LoopPlane) (i : Fin 2) (z : LoopPlane) : E :=
  coneCartesianField g r v0 v d (polarCoordinates x z).1 (polarCoordinates x z).2 i




theorem coneDiskMap_polar {M : Type*} (P : C → M)
    (r : ℝ) (v0 : C)
    (v : ℝ → C) (x : LoopPlane) {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    coneDiskMap P r v0 v x (polarPlane x p) = P (coneCoordinates r v0 v p.1 p.2) := by
  simp only [coneDiskMap, polarCoordinates_polarPlane x hp]




theorem coneDiskField_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : C → E) (r : ℝ)
    (v0 : C) (v d : ℝ → C)
    (x : LoopPlane) (i : Fin 2) {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    coneDiskField g r v0 v d x i (polarPlane x p) =
      coneCartesianField g r v0 v d p.1 p.2 i := by
  simp only [coneDiskField, polarCoordinates_polarPlane x hp]

end PoincareConjecture.M64BoundaryCone
