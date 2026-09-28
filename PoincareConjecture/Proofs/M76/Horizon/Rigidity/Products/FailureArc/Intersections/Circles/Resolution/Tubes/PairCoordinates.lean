import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.ProjectedCrossingCoordinates

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

theorem exists_whole_pair_coordinates
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {A B : Set X} {y : X}
    (C : OriginalSurfacePairChart e A B y false)
    (W : Set X) (hW : IsOpen W) (hyW : y ∈ W) :
    ∃ T : OpenPartialHomeomorph X (Fin 3 → ℝ), y ∈ T.source ∧ T.source ⊆ W ∧
      (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
      (∀ z ∈ T.source, z ∈ A ↔ T z 0 = 0) ∧
      (∀ z ∈ T.source, z ∈ B ↔ T z 1 = 0) := by
  let Q := C.chart.trans (C.coordinates.trans crossingCoordinatesLeftLast.toHomeomorph.toOpenPartialHomeomorph)
  let T := Q.restrOpen W hW
  have hsource {z : X} (hz : z ∈ T.source) :
      z ∈ C.chart.source ∧ C.chart z ∈ C.coordinates.source := ⟨hz.1.1,hz.1.2.1⟩
  refine ⟨T,⟨⟨C.center_source,C.center_coordinates,mem_univ _⟩,hyW⟩,
    fun _ hz => hz.2,?_,?_,?_⟩
  · intro i
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have hcoord := (locallyPiecewiseAffineOn_affine
      crossingCoordinatesLeftLast.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp
      C.forwardPL
    have h := hcoord.comp (C.compatible i).1
    exact h.mono ((e i).symm.trans T).open_source
      (fun z hz => ⟨⟨hz.1,(hsource hz.2).1⟩,(hsource hz.2).2,mem_univ _⟩)
  · intro z hz
    change z ∈ A ↔ (C.coordinates (C.chart z)).2 = 0
    have hh := C.first_surface (C.chart z) (hsource hz).2
    rw [C.chart.left_inv (hsource hz).1] at hh
    simpa only [Bool.false_eq_true, false_implies, and_true] using hh
  · intro z hz
    change z ∈ B ↔ (C.coordinates (C.chart z)).1.1 = 0
    have hh := C.second_surface (C.chart z) (hsource hz).2
    rw [C.chart.left_inv (hsource hz).1] at hh
    simpa only [Bool.false_eq_true, false_implies, and_true] using hh

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
