import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedraSubcomplexes
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.SupportedFinitePLExtension
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallPairs

/-!
# Mark an actual disk and edge in one planar-coordinate refinement

Extend the disk's finite PL parameters to the finite ambient carrier,
make them face-affine, and mark both the disk and the old edge. The
disk chart remains injective and sends its rim complement to the
interior of its exact image. See Hudson 1969, pp. 12--19.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Construct a common refinement retaining a disk and a specified
face, together with actual face-affine disk coordinates. -/
theorem exists_marked_disk_face_refinement
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {d q : Set E} (hd : IsFinitePLBallPair F d q) (hdK : d ⊆ K.space)
    {s : Finset E} (hs : s ∈ K.faces) :
    ∃ (R D A : SimplicialComplex ℝ E) (g : E → F),
      R.faces.Finite ∧ R.IsSubdivision K ∧ D ≤ R ∧ D.space = d ∧
      A ≤ R ∧ A.space = convexHull ℝ (s : Set E) ∧
      R.AffineOnFaces g ∧ InjOn g D.space ∧
      ∀ x ∈ d \ q, g x ∈ interior (g '' D.space) := by
  classical
  obtain ⟨_, C, hC, _, _, H, hH, hboundary⟩ := hd
  obtain ⟨f, hf, hHval⟩ := hH
  obtain ⟨g, hg, hgf, _, _⟩ := hf.exists_supported_extension K hK hdK
    isOpen_univ (subset_univ _)
  obtain ⟨T, hT, hTs, hgT⟩ := hg
  obtain ⟨N, hN, hNK, hNT⟩ := K.exists_common_finite_subdivision T hK hT hTs.symm
  obtain ⟨B, hB, hBs, _⟩ := hf
  let A : SimplicialComplex ℝ E :=
    { faces := {u | u ∈ K.faces ∧ u ⊆ s}
      indep := fun hu => K.indep hu.1
      isRelLowerSet_faces := by
        intro u hu
        exact ⟨K.nonempty_of_mem_faces hu.1, fun v hv hne =>
          ⟨K.down_closed hu.1 hv hne, hv.trans hu.2⟩⟩
      inter_subset_convexHull := fun hu hv => K.inter_subset_convexHull hu.1 hv.1 }
  have hA : A.faces.Finite := hK.subset (fun _ hu => hu.1)
  have hAs : A.space = convexHull ℝ (s : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, hxu⟩ := mem_space_iff.mp hx
      exact convexHull_mono hu.2 hxu
    · intro hx
      exact mem_space_iff.mpr ⟨s, ⟨hs, Finset.Subset.rfl⟩, hx⟩
  let pieces : Bool → SimplicialComplex ℝ E := fun b => if b then B else A
  have hpieces (b : Bool) : (pieces b).faces.Finite := by
    cases b <;> assumption
  have hpiecesN (b : Bool) : (pieces b).space ⊆ N.space := by
    cases b
    · exact hAs.subset.trans ((K.convexHull_subset_space hs).trans hNK.space_eq.symm.subset)
    · exact hBs.subset.trans (hdK.trans hNK.space_eq.symm.subset)
  obtain ⟨R, L, hR, hRN, hL⟩ :=
    N.exists_subdivision_with_finite_polyhedra hN pieces hpieces hpiecesN
  have hDs : (L true).space = d := (hL true).2.trans hBs
  have hEs : (L false).space = convexHull ℝ (s : Set E) := (hL false).2.trans hAs
  have hrep (x : d) : g x = (H x : F) := (hgf x.property).trans (hHval x).symm
  have himage : g '' (L true).space = C := by
    rw [hDs]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hrep ⟨x, hx⟩]
      exact (H ⟨x, hx⟩).property
    · intro y hy
      obtain ⟨x, hx⟩ := H.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (hrep x).trans (congrArg Subtype.val hx)⟩
  refine ⟨R, L true, L false, g, hR, hRN.trans hNK, (hL true).1, hDs,
    (hL false).1, hEs, hRN.affineOnFaces (hNT.affineOnFaces hgT), ?_, ?_⟩
  · intro x hx y hy hxy
    have hxD := hDs.subset hx
    have hyD := hDs.subset hy
    rw [hrep ⟨x, hxD⟩, hrep ⟨y, hyD⟩] at hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext hxy))
  · intro x hx
    rw [himage, hrep ⟨x, hx.1⟩]
    by_contra hnot
    exact hx.2 ((hboundary ⟨x, hx.1⟩).mpr
      ⟨subset_closure (H ⟨x, hx.1⟩).property, hnot⟩)

end Geometry.SimplicialComplex
