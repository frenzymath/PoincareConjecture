import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapBandGluing
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcRelativeBoundaryCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_coordinate_face_covers_arc_near_edge
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0) (hp : p ∈ Ioo (0 : ℝ) T)
    {D U V : Set AnnulusCoordinates} (hD : IsCompact D) (hpD : gamma p ∉ D)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc 0 T ∪ D)
    (hfV : frontier V = gamma '' Icc 0 T ∪ D)
    (face : SmoothFace AnnulusCoordinates)
    (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (basis : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : convexHull ℝ (range basis) ⊆ C.source)
    (hcarrier : face.carrier = C '' convexHull ℝ (range basis))
    (hboundary : ∀ k : Fin 3, (face.boundary k).map = C ∘
      affineChartSegment (basis (k.succAbove 0)) (basis (k.succAbove 1)))
    (hsub : face.carrier ⊆ closure U) (k : Fin 3)
    (hedge : (face.boundary k).map '' Icc (0 : ℝ) 1 ⊆ gamma '' Icc 0 T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (htp : (face.boundary k).map t = gamma p) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma p ∈ W ∧ W ∩ closure U ⊆ face.carrier := by
  let other := ⋃ j : {j : Fin 3 // j ≠ k}, (face.boundary j).map '' Icc (0 : ℝ) 1
  have hcompact : IsCompact other := isCompact_iUnion (fun j =>
    isCompact_Icc.image_of_continuousOn (face.boundary j).smooth.continuousOn)
  have hpOther : gamma p ∉ other := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact coordinate_triangle_boundary_avoids_other_edges face C basis hsource hboundary
      (Ne.symm j.property) ht (htp.symm ▸ hj)
  have hregularFace : closure (interior face.carrier) = face.carrier := by
    rw [hcarrier]
    exact coordinate_triangle_closure_interior C basis hsource
  have hpFace : gamma p ∈ face.carrier := face.isClosed_carrier.frontier_subset
    (face.boundary_image_subset_frontier k ⟨t, Ioo_subset_Icc_self ht, htp⟩)
  apply m64Intrinsic_exists_arc_relative_cover_of_local_frontier hg hinj hregular hp
    hD hpD hU hV hdisj hfU hfV face.isClosed_carrier hregularFace hsub hpFace
    (hcompact.isClosed.isOpen_compl.mem_nhds hpOther)
  rintro z ⟨hzOther, hzFront⟩
  rw [face.boundary_carrier] at hzFront
  obtain ⟨j, hj⟩ := mem_iUnion.mp hzFront
  by_cases hjk : j = k
  · exact Or.inl (hedge (hjk ▸ hj))
  · exact False.elim (hzOther (mem_iUnion.mpr ⟨⟨j, hjk⟩, hj⟩))

end PoincareConjecture
