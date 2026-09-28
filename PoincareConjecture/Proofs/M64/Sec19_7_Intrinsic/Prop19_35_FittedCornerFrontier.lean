import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FittedCornerCap
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Affine.Lines

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_corner_face_frontier_subset
    {gamma : ℝ → AnnulusCoordinates} {T r : ℝ}
    (hr : 0 < r) (hrT : r ≤ T)
    {H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates}
    (haxis : ∀ s : ℝ, H (s, 0) = gamma s)
    (haxis' : ∀ s : ℝ, H (0, s) = gamma (T - s))
    {face : SmoothFace AnnulusCoordinates}
    (hfirst : ∀ t ∈ Icc (0 : ℝ) 1, (face.boundary 2).map t = H (t * r, 0))
    (hsecond : ∀ t ∈ Icc (0 : ℝ) 1, (face.boundary 1).map t = H (0, t * r)) :
    frontier face.carrier ⊆ gamma '' Icc 0 T ∪
      (face.boundary 0).map '' Icc (0 : ℝ) 1 := by
  intro z hz
  rw [face.boundary_carrier] at hz
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  obtain ⟨t, ht, rfl⟩ := hk
  fin_cases k
  · exact Or.inr ⟨t, ht, by rfl⟩
  · left
    change (face.boundary 1).map t ∈ gamma '' Icc 0 T
    rw [hsecond t ht, haxis' (t * r)]
    refine ⟨T - t * r, ?_, rfl⟩
    constructor <;> nlinarith [ht.1, ht.2, hr, hrT]
  · left
    change (face.boundary 2).map t ∈ gamma '' Icc 0 T
    rw [hfirst t ht, haxis (t * r)]
    refine ⟨t * r, ?_, rfl⟩
    constructor <;> nlinarith [ht.1, ht.2, hr, hrT]

theorem m64Intrinsic_corner_face_chord_line
    {H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates}
    {face : SmoothFace AnnulusCoordinates} {r : ℝ}
    (hchord : ∀ t : ℝ, (face.boundary 0).map t =
      (1 - t) • H (r, 0) + t • H (0, r)) :
    ∃ l : AnnulusCoordinates →ᵃ[ℝ] ℝ,
      Function.Surjective l ∧
        (face.boundary 0).map '' Icc (0 : ℝ) 1 ⊆ {z | l z = 0} := by
  obtain ⟨l, hl, hline⟩ :=
    Poincare.Topology.Plane.exists_affine_line_containing_segment (H (r, 0)) (H (0, r))
  refine ⟨l, hl, ?_⟩
  rintro z ⟨t, ht, rfl⟩
  rw [hchord]
  apply hline
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  module

end PoincareConjecture
