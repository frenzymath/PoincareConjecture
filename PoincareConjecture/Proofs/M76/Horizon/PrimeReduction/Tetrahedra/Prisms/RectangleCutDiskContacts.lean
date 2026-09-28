import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalRectangleBoundaryCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.FaceRegionIncidence

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem exists_original_rectangle_cut_disk_contacts
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [Finite ι] [DecidableEq ι]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    (cut rim : ι → Set E) (hcut : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (cut i) (rim i))
    (hsub : ∀ i, cut i ⊆ convexHull ℝ (t : Set E))
    (hrim : ∀ i, cut i ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = rim i)
    (hdis : Pairwise fun i j => Disjoint (cut i) (cut j))
    (hphysical : g '' (⋃ i, cut i) = S ∩ (g '' convexHull ℝ (t : Set E))) :
    ∃ owner : ∀ f : TetrahedronFace K t, (D f).Arc → ι,
      (∀ f j, (D f).arc j ⊆ rim (owner f j)) ∧
      (∀ f j i, i ≠ owner f j → Disjoint ((D f).arc j) (cut i)) ∧
      (∀ i, rim i = ⋃ f : TetrahedronFace K t, ⋃ j : {j // owner f j = i}, (D f).arc j) ∧
      ∀ f k i, (D f).carrier k ∩ cut i =
        (if owner f ((D f).cap k false) = i then (D f).arc ((D f).cap k false) else ∅) ∪
        (if owner f ((D f).cap k true) = i then (D f).arc ((D f).cap k true) else ∅) := by
  classical
  have hcutSub : (⋃ i, cut i) ⊆ convexHull ℝ (t : Set E) := iUnion_subset hsub
  have hfacet (f : TetrahedronFace K t) : convexHull ℝ (f.1.1 : Set E) ⊆
      intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) := by
    apply (K.indep ht).convexHull_subset_intrinsicFrontier
    exact Finset.ssubset_iff_subset_ne.mpr ⟨f.2,fun he => by
      have hc := congrArg Finset.card he
      rw [f.1.2.2,ht4] at hc
      omega⟩
  have harcSub (f : TetrahedronFace K t) (j : (D f).Arc) :
      (D f).arc j ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∩ ⋃ i, cut i := by
    intro x hx
    have hxF := (D f).arcSubset (mem_iUnion.mpr ⟨j,hx⟩)
    refine ⟨hfacet f hxF,?_⟩
    apply (original_face_cut_mem_iff K g hgi ht hcutSub hphysical
      (convexHull_mono f.2 hxF)).mpr
    exact ((D f).arcPhysical.subset (mem_image_of_mem g (mem_iUnion.mpr ⟨j,hx⟩))).1
  choose owner howner hother using fun f => exists_face_arc_disk_owners cut rim
    (D f).arc (D f).rim hcut hrim hdis (D f).arcBall (harcSub f)
  have hownerCut (f : TetrahedronFace K t) (j : (D f).Arc) :
      (D f).arc j ⊆ cut (owner f j) := (howner f j).trans (hcut _).1
  refine ⟨owner,howner,hother,?_,?_⟩
  · intro i
    ext x
    constructor
    · intro hx
      have hxcut := (hcut i).1 hx
      have hxF := ((hrim i).symm.subset hx).2
      obtain ⟨v,hv,hxv⟩ := ((K.indep ht).mem_intrinsicFrontier_convexHull_finset
        (K.nonempty_of_mem_faces ht) x).mp hxF
      have hs3 : (t.erase v).card = 3 := by rw [Finset.card_erase_of_mem hv,ht4]
      have hs : t.erase v ∈ K.faces := K.down_closed ht (Finset.erase_subset _ _)
        (Finset.card_pos.mp (by omega))
      let f : TetrahedronFace K t := ⟨⟨t.erase v,hs,hs3⟩,Finset.erase_subset _ _⟩
      have hxS : g x ∈ S := (hphysical.subset (mem_image_of_mem g (mem_iUnion.mpr ⟨i,hxcut⟩))).1
      have hxarc := (original_face_cut_mem_iff K g hgi hs (D f).arcSubset
        (D f).arcPhysical hxv).mpr hxS
      obtain ⟨j,hxj⟩ := mem_iUnion.mp hxarc
      have hj : owner f j = i := by
        by_contra hne
        exact disjoint_left.mp (hdis hne) (hownerCut f j hxj) hxcut
      exact mem_iUnion.mpr ⟨f,mem_iUnion.mpr ⟨⟨j,hj⟩,hxj⟩⟩
    · intro hx
      obtain ⟨f,hxf⟩ := mem_iUnion.mp hx
      obtain ⟨j,hxj⟩ := mem_iUnion.mp hxf
      exact j.2 ▸ howner f j hxj
  · intro f k i
    have hcontact : (D f).carrier k ∩ (⋃ i, cut i) =
        (D f).arc ((D f).cap k false) ∪ (D f).arc ((D f).cap k true) := by
      rw [←(D f).cutContact k]
      ext x
      constructor
      · rintro ⟨hxM,hxcut⟩
        exact ⟨hxM,(original_face_cut_mem_iff K g hgi f.1.2.1 (D f).arcSubset
          (D f).arcPhysical ((D f).carrier_subset_face k hxM)).mpr
          ((hphysical.subset (mem_image_of_mem g hxcut)).1)⟩
      · rintro ⟨hxM,hxarc⟩
        obtain ⟨j,hxj⟩ := mem_iUnion.mp hxarc
        exact ⟨hxM,(harcSub f j hxj).2⟩
    have hsingle (j : (D f).Arc) : (D f).arc j ∩ cut i =
        if owner f j = i then (D f).arc j else ∅ := by
      split_ifs with hj
      · exact inter_eq_left.mpr (hj ▸ hownerCut f j)
      · exact disjoint_iff_inter_eq_empty.mp (hother f j i (Ne.symm hj))
    have he : (D f).carrier k ∩ cut i =
        ((D f).carrier k ∩ (⋃ i, cut i)) ∩ cut i := by
      ext x
      constructor
      · exact fun hx => ⟨⟨hx.1,mem_iUnion.mpr ⟨i,hx.2⟩⟩,hx.2⟩
      · exact fun hx => ⟨hx.1.1,hx.2⟩
    rw [he,hcontact,union_inter_distrib_right,hsingle,hsingle]

end PoincareConjecture.M76.PrismBelt
