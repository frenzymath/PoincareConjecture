import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.OriginalChart.ClippedCarrier
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexNeighborhood
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPreimages



set_option autoImplicit false
open Set Geometry

namespace Geometry

theorem PolyhedralPLInCharts.exists_clipped_interior_disk
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X F}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space) (hinj : InjOn f K.space)
    (Q : OpenPartialHomeomorph X F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    (J P : SimplicialComplex ℝ F) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hP : P.faces.Finite)
    (hPs : P.space = Q '' (f '' K.space ∩ Q.source) ∩ J.space)
    (hinterior : ∀ x ∈ K.space, f x ∈ Q.source →
      Q (f x) ∈ interior J.space → x ∈ interior K.space)
    {w : F} (hw : w ∈ P.space) (hwJ : w ∈ interior J.space) :
    ∃ d rim : Set F, IsFinitePLBallPair E d rim ∧ d ⊆ P.space ∧
      w ∈ d \ rim ∧ IsOpen ((Subtype.val : P.space → F) ⁻¹' (d \ rim)) := by
  obtain ⟨g, hg, hgK, hgi, hright, _, himage⟩ :=
    hf.exists_clipped_source_parameter K hK hinj Q hQ J P hJ hJQ hP hPs
  obtain ⟨H, hH, hHval⟩ := hg.exists_homeomorph_image hgi
  let O : Set K.space := (fun x => f x) ⁻¹' (Q.source ∩ Q ⁻¹' interior J.space)
  have hO : IsOpen O := (Q.isOpen_inter_preimage isOpen_interior).preimage
    hf.continuousOn.domRestrict
  have hgwO : (⟨g w, hgK hw⟩ : K.space) ∈ O := by
    change f (g w) ∈ Q.source ∧ Q (f (g w)) ∈ interior J.space
    rw [hright w hw]
    exact ⟨Q.map_target (hJQ (interior_subset hwJ)),
      (Q.right_inv (hJQ (interior_subset hwJ))).symm ▸ hwJ⟩
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hO
  have hgwU : g w ∈ U := (Set.ext_iff.mp hUeq ⟨g w, hgK hw⟩).mpr hgwO
  have hgwint : g w ∈ interior K.space := hinterior _ (hgK hw) hgwO.1 hgwO.2
  obtain ⟨B, hB, hBcv, hgwB, hBU⟩ :=
    (isOpen_interior.inter hU).exists_finite_convex_neighborhood ⟨hgwint, hgwU⟩
  have hpair : IsFinitePLBallPair E B.space (frontier B.space) :=
    isFinitePLBallPair_of_compact_convex (B.isCompact_space_of_finite hB)
      hBcv ⟨g w, hgwB⟩ B hB rfl
  have hBimage : B.space ⊆ g '' P.space := by
    intro x hx
    have hxK := interior_subset (hBU hx).1
    have hxO : (⟨x, hxK⟩ : K.space) ∈ O :=
      (Set.ext_iff.mp hUeq ⟨x, hxK⟩).mp (hBU hx).2
    exact himage.symm.subset ⟨hxK, hxO.1, interior_subset hxO.2⟩
  let d := P.space ∩ g ⁻¹' B.space
  let rim := P.space ∩ g ⁻¹' frontier B.space
  have hball : IsFinitePLBallPair E d rim := hH.preimage_ballPair hpair hBimage hHval
  have heq : d \ rim = P.space ∩ g ⁻¹' interior B.space := by
    rw [← self_sdiff_frontier B.space]
    ext x
    simp only [d, rim, mem_sdiff, mem_inter_iff, mem_preimage]
    tauto
  refine ⟨d, rim, hball, inter_subset_left, ?_, ?_⟩
  · rw [heq]
    exact ⟨hw, hgwB⟩
  · have hpull : (Subtype.val : P.space → F) ⁻¹' (d \ rim) =
        (fun x : P.space => g x) ⁻¹' interior B.space := by
      rw [heq]
      ext x
      simp only [mem_preimage, mem_inter_iff, x.property, true_and]
    rw [hpull]
    exact isOpen_interior.preimage hg.continuousOn.domRestrict

end Geometry
