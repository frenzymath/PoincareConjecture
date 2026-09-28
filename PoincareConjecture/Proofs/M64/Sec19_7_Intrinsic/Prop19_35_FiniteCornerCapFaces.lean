import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteCornerCapData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChosenCapGeometry
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapCompatibility




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture




structure M64IntrinsicFiniteCornerCapFaces
    {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
    {U : Set AnnulusCoordinates} (C : M64IntrinsicFiniteCornerCaps alpha beta A B U) where
  face : J → Bool × Bool → SmoothFace AnnulusCoordinates
  coordinates : J → Bool × Bool → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates
  basis : J → Bool × Bool → AffineBasis (Fin 3) ℝ AnnulusCoordinates
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

namespace M64IntrinsicFiniteCornerCaps

variable {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
  {U : Set AnnulusCoordinates} (C : M64IntrinsicFiniteCornerCaps alpha beta A B U)





theorem axes_subset_frontier (j : J) :
    (fun t : ℝ => C.chart j (0, t * C.radius j)) '' Icc 0 1 ∪
      (fun t : ℝ => C.chart j (t * C.radius j, 0)) '' Icc 0 1 ⊆ frontier U := by
  have hparam (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t * C.radius j ∈ Icc 0 (C.radius j) :=
    ⟨mul_nonneg ht.1 (C.radius_pos j).le, mul_le_of_le_one_left (C.radius_pos j).le ht.2⟩
  rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
  · change C.chart j (0, t * C.radius j) ∈ frontier U
    rw [C.second_axis]
    have h : beta j (t * C.radius j) ∈ C.carrier j ∩ frontier U := by
      rw [C.frontier_contact]
      exact Or.inr ⟨t * C.radius j, hparam t ht, rfl⟩
    exact h.2
  · change C.chart j (t * C.radius j, 0) ∈ frontier U
    rw [C.first_axis]
    have h : alpha j (t * C.radius j) ∈ C.carrier j ∩ frontier U := by
      rw [C.frontier_contact]
      exact Or.inl ⟨t * C.radius j, hparam t ht, rfl⟩
    exact h.2




theorem exists_faces : Nonempty (M64IntrinsicFiniteCornerCapFaces C) := by
  classical
  choose face hface hzero hone htwo Q b hQ hQi hsource hcarrier hboundary using
    fun (j : J) (i : Bool × Bool) => m64Intrinsic_exists_coordinate_face_of_chosen_cap
      (C.cap j i) (C.radius_pos j) (C.cap_source j i) (C.cap_smooth j i) (C.cap_inverse_smooth j i)
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

end M64IntrinsicFiniteCornerCaps

namespace M64IntrinsicFiniteCornerCapFaces

variable {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
  {U : Set AnnulusCoordinates} {C : M64IntrinsicFiniteCornerCaps alpha beta A B U}
  (F : M64IntrinsicFiniteCornerCapFaces C)




theorem occupied_union (j : J) :
    (⋃ i, ⋃ (_ : if C.positive j then i = (true, true) else i ≠ (true, true)),
      (F.face j i).carrier) = C.carrier j := by
  simp only [F.original_carrier]




theorem sector (j : J) (i : Bool × Bool) :
    (F.face j i).carrier ⊆ C.chart j '' ((C.chart j).source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
  rw [F.original_carrier]
  exact C.cap_sector j i




theorem second (j : J) (i : Bool × Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((F.face j i).boundary 1).map t =
      C.chart j (sectorParameterEquiv 0 i (0, t * C.radius j)) := by
  rw [F.original_one]
  exact C.cap_second j i _ ⟨mul_nonneg ht.1 (C.radius_pos j).le,
    mul_le_of_le_one_left (C.radius_pos j).le ht.2⟩




theorem first (j : J) (i : Bool × Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((F.face j i).boundary 2).map t =
      C.chart j (sectorParameterEquiv 0 i (t * C.radius j, 0)) := by
  rw [F.original_two]
  exact C.cap_first j i _ ⟨mul_nonneg ht.1 (C.radius_pos j).le,
    mul_le_of_le_one_left (C.radius_pos j).le ht.2⟩




theorem chord (j : J) (i : Bool × Bool) (t : ℝ) : ((F.face j i).boundary 0).map t =
    (1 - t) • C.chart j (sectorParameterEquiv 0 i (C.radius j, 0)) +
      t • C.chart j (sectorParameterEquiv 0 i (0, C.radius j)) := by
  rw [F.original_zero, C.cap_chord,
    C.cap_first j i (C.radius j) ⟨(C.radius_pos j).le, le_rfl⟩,
    C.cap_second j i (C.radius j) ⟨(C.radius_pos j).le, le_rfl⟩]





theorem canonical (e : J) (i j : Bool × Bool) (hij : i ≠ j) :
    CoordinateTriangleBoundaryIntersection (F.coordinates e i) (F.coordinates e j)
      (F.basis e i) (F.basis e j) := by
  apply m64Intrinsic_retained_caps_canonical_compatibility (C.chart e) (C.radius_pos e)
    (F.face e) (F.coordinates e) (F.basis e) (F.carrier e) (F.boundary e) (F.sector e)
    (fun i => ?_) (C.axes_source e) (F.second e) (F.first e) i j hij
  rw [F.original_carrier]
  exact C.cap_axis_contact e i

end M64IntrinsicFiniteCornerCapFaces

end PoincareConjecture
