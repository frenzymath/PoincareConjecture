import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCapData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChosenCapGeometry
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapCompatibility





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture




structure M64IntrinsicThreeArcCapFaces
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    (C : M64IntrinsicThreeArcCaps gamma sigma T S U) where
  face : Bool → Bool × Bool → SmoothFace AnnulusCoordinates
  coordinates : Bool → Bool × Bool → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates
  basis : Bool → Bool × Bool → AffineBasis (Fin 3) ℝ AnnulusCoordinates
  smooth : ∀ e i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (coordinates e i) (coordinates e i).source
  inverse_smooth : ∀ e i,
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (coordinates e i).symm (coordinates e i).target
  source : ∀ e i, convexHull ℝ (range (basis e i)) ⊆ (coordinates e i).source
  carrier : ∀ e i, (face e i).carrier = coordinates e i '' convexHull ℝ (range (basis e i))
  boundary : ∀ e i k, ((face e i).boundary k).map = coordinates e i ∘
    affineChartSegment (basis e i (k.succAbove 0)) (basis e i (k.succAbove 1))
  original_carrier : ∀ e i, (face e i).carrier =
    C.cap e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ C.radius e}
  original_zero : ∀ e i (t : ℝ), ((face e i).boundary 0).map t =
    C.cap e i ((1 - t) * C.radius e, t * C.radius e)
  original_one : ∀ e i (t : ℝ), ((face e i).boundary 1).map t = C.cap e i (0, t * C.radius e)
  original_two : ∀ e i (t : ℝ), ((face e i).boundary 2).map t = C.cap e i (t * C.radius e, 0)

namespace M64IntrinsicThreeArcCaps




theorem exists_faces
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    (C : M64IntrinsicThreeArcCaps gamma sigma T S U) :
    Nonempty (M64IntrinsicThreeArcCapFaces C) := by
  classical
  choose face hface hzero hone htwo Q b hQ hQi hsource hcarrier hboundary using
    fun (e : Bool) (i : Bool × Bool) => m64Intrinsic_exists_coordinate_face_of_chosen_cap
      (C.cap e i) (C.radius_pos e) (C.cap_source e i) (C.cap_smooth e i) (C.cap_inverse_smooth e i)
  exact ⟨{
    face := face
    coordinates := Q
    basis := b
    smooth := hQ
    inverse_smooth := hQi
    source := hsource
    carrier := hcarrier
    boundary := hboundary
    original_carrier := hface
    original_zero := hzero
    original_one := hone
    original_two := htwo }⟩

end M64IntrinsicThreeArcCaps

namespace M64IntrinsicThreeArcCapFaces

variable {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
  {T : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
  {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
  (A : M64IntrinsicThreeArcCapFaces C)




theorem occupied_union (e : Bool) :
    (⋃ i, ⋃ (_ : if C.positive e then i = (true, true) else i ≠ (true, true)),
      (A.face e i).carrier) = C.carrier e := by
  simp only [A.original_carrier]




theorem sector (e : Bool) (i : Bool × Bool) :
    (A.face e i).carrier ⊆ C.chart e '' ((C.chart e).source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
  rw [A.original_carrier]
  exact C.cap_sector e i




theorem second (e : Bool) (i : Bool × Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((A.face e i).boundary 1).map t =
      C.chart e (sectorParameterEquiv 0 i (0, t * C.radius e)) := by
  rw [A.original_one]
  exact C.cap_second e i _ ⟨mul_nonneg ht.1 (C.radius_pos e).le,
    mul_le_of_le_one_left (C.radius_pos e).le ht.2⟩




theorem first (e : Bool) (i : Bool × Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((A.face e i).boundary 2).map t =
      C.chart e (sectorParameterEquiv 0 i (t * C.radius e, 0)) := by
  rw [A.original_two]
  exact C.cap_first e i _ ⟨mul_nonneg ht.1 (C.radius_pos e).le,
    mul_le_of_le_one_left (C.radius_pos e).le ht.2⟩




theorem chord (e : Bool) (i : Bool × Bool) (t : ℝ) : ((A.face e i).boundary 0).map t =
    (1 - t) • C.chart e (sectorParameterEquiv 0 i (C.radius e, 0)) +
      t • C.chart e (sectorParameterEquiv 0 i (0, C.radius e)) := by
  rw [A.original_zero, C.cap_chord,
    C.cap_first e i (C.radius e) ⟨(C.radius_pos e).le, le_rfl⟩,
    C.cap_second e i (C.radius e) ⟨(C.radius_pos e).le, le_rfl⟩]




theorem canonical (e : Bool) (i j : Bool × Bool) (hij : i ≠ j) :
    CoordinateTriangleBoundaryIntersection (A.coordinates e i) (A.coordinates e j)
      (A.basis e i) (A.basis e j) := by
  apply m64Intrinsic_retained_caps_canonical_compatibility (C.chart e) (C.radius_pos e)
    (A.face e) (A.coordinates e) (A.basis e) (A.carrier e) (A.boundary e) (A.sector e)
    (fun i => ?_) (C.axes_source e) (A.second e) (A.first e) i j hij
  rw [A.original_carrier]
  exact C.cap_axis_contact e i

end M64IntrinsicThreeArcCapFaces

end PoincareConjecture
