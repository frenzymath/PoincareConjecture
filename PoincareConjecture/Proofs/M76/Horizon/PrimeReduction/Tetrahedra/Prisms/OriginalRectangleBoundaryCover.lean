import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.CutComponentSidePairing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.MarkedDiskIncidence
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s t : Finset E}

theorem OriginalFaceRectangles.region_core_nonempty
    (D : OriginalFaceRectangles K g S s) (k : D.Region) :
    (D.carrier k \ ⋃ i, D.arc i).Nonempty := by
  obtain ⟨G,_,hW,hZ,_,_⟩ := D.rectangle k
  let p : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
    ⟨(1/2,1/2),by norm_num⟩
  refine ⟨G p,(G p).property,?_⟩
  intro hcut
  rcases (D.cutContact k).subset ⟨(G p).property,hcut⟩ with hw | hz
  · have := (hW p).mp hw
    norm_num [p] at this
  · have := (hZ p).mp hz
    norm_num [p] at this

theorem OriginalFaceRectangles.carrier_subset_face
    (D : OriginalFaceRectangles K g S s) (k : D.Region) :
    D.carrier k ⊆ convexHull ℝ (s : Set E) := by
  obtain ⟨x,hx⟩ := D.region_core_nonempty k
  rw [←(D.componentClosure k x hx).2]
  exact closure_minimal ((connectedComponentIn_subset _ _).trans sdiff_subset)
    (s.finite_toSet.isCompact_convexHull ℝ).isClosed

abbrev CutBallRectangle
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1) (B : Set E) :=
  {z : Σ f : TetrahedronFace K t, (D f).Region // (D z.1).carrier z.2 ⊆ B}

theorem original_regular_region_subset_cut_ball
    (hgi : InjOn g K.space)
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    {B : Set E} (hB : IsClosed B)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (f : TetrahedronFace K t) (k : (D f).Region) {x : E}
    (hx : x ∈ (D f).carrier k \ ⋃ i, (D f).arc i) (hxB : x ∈ B) :
    (D f).carrier k ⊆ B := by
  have hxface := ((D f).componentClosure k x hx).1
  have hxS : g x ∉ S := fun h => hx.2
    ((original_face_cut_mem_iff K g hgi f.1.2.1 (D f).arcSubset
      (D f).arcPhysical hxface.1).mpr h)
  rw [←((D f).componentClosure k x hx).2]
  apply closure_minimal ?_ hB
  apply (connectedComponentIn_mono x ?_).trans
    ((hcomp x ⟨hxB,hxS⟩).subset.trans sdiff_subset)
  intro y hy
  refine ⟨convexHull_mono f.2 hy.1,?_⟩
  intro hyS
  exact hy.2 ((original_face_cut_mem_iff K g hgi f.1.2.1 (D f).arcSubset
    (D f).arcPhysical hy.1).mpr hyS)

theorem cut_ball_boundary_eq_disks_union_rectangles
    (hgi : InjOn g K.space) (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    {B R T : Set E} (hB : IsClosed B)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (hR : R = B ∩ (intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∪ T))
    (hphysical : ∀ x ∈ convexHull ℝ (t : Set E), x ∈ T ↔ g x ∈ S)
    (hregular : ∀ (f : TetrahedronFace K t)
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i : Set E)),
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional) :
    R = (B ∩ T) ∪ ⋃ z : CutBallRectangle D B, (D z.1.1).carrier z.1.2 := by
  have hfacet (f : TetrahedronFace K t) : convexHull ℝ (f.1.1 : Set E) ⊆
      intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) := by
    apply (K.indep ht).convexHull_subset_intrinsicFrontier
    exact Finset.ssubset_iff_subset_ne.mpr ⟨f.2,fun he => by
      have hc := congrArg Finset.card he
      rw [f.1.2.2,ht4] at hc
      omega⟩
  rw [hR]
  ext x
  constructor
  · rintro ⟨hxB,hxF | hxT⟩
    · by_cases hxT : x ∈ T
      · exact Or.inl ⟨hxB,hxT⟩
      have hxS : g x ∉ S := fun h => hxT ((hphysical x
        (intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed hxF)).mpr h)
      obtain ⟨v,hv,hxv⟩ := ((K.indep ht).mem_intrinsicFrontier_convexHull_finset
        (K.nonempty_of_mem_faces ht) x).mp hxF
      have hs3 : (t.erase v).card = 3 := by rw [Finset.card_erase_of_mem hv,ht4]
      have hs : t.erase v ∈ K.faces := K.down_closed ht (Finset.erase_subset _ _)
        (Finset.card_pos.mp (by omega))
      let f : TetrahedronFace K t := ⟨⟨t.erase v,hs,hs3⟩,Finset.erase_subset _ _⟩
      have hxface : x ∈ convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i :=
        ⟨hxv,fun hxcut => hxS (((D f).arcPhysical.subset (mem_image_of_mem g hxcut)).1)⟩
      obtain ⟨k,hxk,_⟩ := ((D f).regionLabels ⟨x,hxface⟩).mp (hregular f ⟨x,hxface⟩ hxB)
      have hk := original_regular_region_subset_cut_ball hgi D hB hcomp f k hxk hxB
      exact Or.inr (mem_iUnion.mpr ⟨⟨⟨f,k⟩,hk⟩,hxk.1⟩)
    · exact Or.inl ⟨hxB,hxT⟩
  · rintro (⟨hxB,hxT⟩ | hxM)
    · exact ⟨hxB,Or.inr hxT⟩
    · obtain ⟨z,hxz⟩ := mem_iUnion.mp hxM
      exact ⟨z.2 hxz,Or.inl (hfacet z.1.1 ((D z.1.1).carrier_subset_face z.1.2 hxz))⟩

end PoincareConjecture.M76.PrismBelt
