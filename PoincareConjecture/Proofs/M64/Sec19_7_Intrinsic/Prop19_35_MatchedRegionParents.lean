import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandChainCompatibility
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RetainedCoreMatching















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture







theorem m64Intrinsic_exists_cap_band_core_coordinate_parents
    {I J : Type*} [Finite I] [Finite J]
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (lo : I → ℝ → ℝ) (a b ua wa ub wb ra rb : I → ℝ)
    (B : ∀ i, ObliqueBandFaces (F i) (lo i) (a i) (b i)
      (ua i) (wa i) (ub i) (wb i) (ra i) (rb i))
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hBB : ∀ (p q : (i : I) × (Fin (B i).interface.count × Bool)), p ≠ q →
      CoordinateTriangleBoundaryIntersection
        ((B p.1).faceCoordinates p.2) ((B q.1).faceCoordinates q.2)
        ((B p.1).faceBasis p.2) ((B q.1).faceBasis q.2))
    (hcuts : ∀ i (right : Bool), ∃ u v : AnnulusCoordinates,
      ((B i).endpointEdge right).map '' Icc (0 : ℝ) 1 = segment ℝ u v)
    (G : J → OpenPartialHomeomorph Plane AnnulusCoordinates)
    (d : J → AffineBasis (Fin 3) ℝ Plane)
    (hG : ∀ j, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (G j) (G j).source)
    (hGi : ∀ j, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (G j).symm (G j).target)
    (hsource : ∀ j, convexHull ℝ (range (d j)) ⊆ (G j).source)
    (hGG : ∀ j k, j ≠ k → CoordinateTriangleBoundaryIntersection (G j) (G k) (d j) (d k))
    (k : J → Fin 3) (u v : J → AnnulusCoordinates)
    (hchord : ∀ j, G j '' affineSegment ℝ (d j ((k j).succAbove 0))
      (d j ((k j).succAbove 1)) = segment ℝ (u j) (v j))
    (houter : ∀ i j, (B i).carrier ∩ (G j '' convexHull ℝ (range (d j))) ⊆
      (B i).leftCut ∪ (B i).rightCut)
    (hcap : ∀ i j, (B i).carrier ∩ (G j '' convexHull ℝ (range (d j))) ⊆
      G j '' affineSegment ℝ (d j ((k j).succAbove 0)) (d j ((k j).succAbove 1)))
    (T : TriangleMesh)
    (hcorecap : ∀ (t : T.Triangle) j,
      CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
        (G j) (meshTriangleBasis T t) (d j))
    (hcoreband : ∀ (t : T.Triangle) i (p : Fin (B i).interface.count × Bool),
      CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
        ((B i).faceCoordinates p) (meshTriangleBasis T t) ((B i).faceBasis p)) :
    ∃ (m : ℕ) (C : Fin m → OpenPartialHomeomorph Plane AnnulusCoordinates)
      (c : Fin m → AffineBasis (Fin 3) ℝ Plane),
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p) (C p).source) ∧
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p).symm (C p).target) ∧
      (∀ p, convexHull ℝ (range (c p)) ⊆ (C p).source) ∧
      (∀ p q, p ≠ q → CoordinateTriangleBoundaryIntersection (C p) (C q) (c p) (c q)) ∧
      (⋃ p, C p '' convexHull ℝ (range (c p))) =
        ((⋃ j, G j '' convexHull ℝ (range (d j))) ∪ ⋃ i, (B i).carrier) ∪
          T.toPlaneComplex.support := by
  classical
  choose M hsupport _ hcontact using fun i =>
    m64Intrinsic_refine_band_faces_to_chord_family (B i) (hcuts i) G d hsource
      k u v hchord (houter i) (hcap i)
  let K := (i : I) × (Fin (B i).interface.count × Bool)
  let E : K → OpenPartialHomeomorph Plane AnnulusCoordinates :=
    fun p => (B p.1).faceCoordinates p.2
  let e : K → AffineBasis (Fin 3) ℝ Plane := fun p => (B p.1).faceBasis p.2
  let mesh : K → TriangleMesh := fun p => M p.1 p.2
  let Child := (p : K) × (mesh p).Triangle
  have hchild (p : Child) : convexHull ℝ (range (meshTriangleBasis (mesh p.1) p.2)) ⊆
      convexHull ℝ (range (e p.1)) := by
    rw [← hsupport p.1.1 p.1.2]
    exact meshTriangleBasis_subset_support (mesh p.1) p.2
  have hEsource (p : K) : convexHull ℝ (range (e p)) ⊆ (E p).source :=
    (B p.1).face_triangle_subset_source p.2
  obtain ⟨hchildren, hcover⟩ := m64Intrinsic_coordinate_mesh_family_canonical
    E e hEsource hBB mesh (fun p => hsupport p.1 p.2)
  let A := J ⊕ (Child ⊕ T.Triangle)
  let C : A → OpenPartialHomeomorph Plane AnnulusCoordinates := Sum.elim G
    (Sum.elim (fun p => E p.1) (fun _ => OpenPartialHomeomorph.refl AnnulusCoordinates))
  let c : A → AffineBasis (Fin 3) ℝ Plane := Sum.elim d
    (Sum.elim (fun p => meshTriangleBasis (mesh p.1) p.2) (meshTriangleBasis T))
  have hC (p : A) : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p) (C p).source := by
    rcases p with j | p
    · exact hG j
    · rcases p with p | t
      · exact (B p.1.1).smooth_faceCoordinates (hF p.1.1) p.1.2
      · exact contMDiffOn_id
  have hCi (p : A) : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p).symm (C p).target := by
    rcases p with j | p
    · exact hGi j
    · rcases p with p | t
      · exact (B p.1.1).smooth_faceCoordinates_symm (hFi p.1.1) p.1.2
      · exact contMDiffOn_id
  have hCsource (p : A) : convexHull ℝ (range (c p)) ⊆ (C p).source := by
    rcases p with j | p
    · exact hsource j
    · rcases p with p | t
      · exact (hchild p).trans (hEsource p.1)
      · exact subset_univ _
  have hcorechild (t : T.Triangle) (p : Child) :
      CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
        (E p.1) (meshTriangleBasis T t) (meshTriangleBasis (mesh p.1) p.2) :=
    m64Intrinsic_canonical_contact_children _ _ (meshTriangleBasis T t) (e p.1)
      (meshTriangleBasis T t) (meshTriangleBasis (mesh p.1) p.2)
      (subset_univ _) (hEsource p.1) (Subset.refl _) (hchild p)
      (hcoreband t p.1.1 p.1.2)
  have hparents (p q : A) (hpq : p ≠ q) :
      CoordinateTriangleBoundaryIntersection (C p) (C q) (c p) (c q) := by
    rcases p with j | p
    · rcases q with l | q
      · exact hGG j l (fun h => hpq (congrArg Sum.inl h))
      · rcases q with q | t
        · exact (hcontact q.1.1 q.1.2 q.2 j).symm
        · exact (hcorecap t j).symm
    · rcases p with p | t
      · rcases q with j | q
        · exact hcontact p.1.1 p.1.2 p.2 j
        · rcases q with q | s
          · exact hchildren p q (fun h => hpq (congrArg (Sum.inr ∘ Sum.inl) h))
          · exact (hcorechild s p).symm
      · rcases q with j | q
        · exact hcorecap t j
        · rcases q with q | s
          · exact hcorechild t q
          · exact mesh_coordinate_triangle_intersection T
              (OpenPartialHomeomorph.refl AnnulusCoordinates) (subset_univ _) t s
              (fun h => hpq (congrArg (Sum.inr ∘ Sum.inr) h))
  have hbands : (⋃ p : K, E p '' convexHull ℝ (range (e p))) =
      ⋃ i, (B i).carrier := by
    ext x
    simp only [K, E, e, mem_iUnion, Sigma.exists, ← ObliqueBandFaces.face_carrier_eq_coordinates]
    simp only [ObliqueBandFaces.carrier, mem_iUnion]
  have htotal : (⋃ p : A, C p '' convexHull ℝ (range (c p))) =
      ((⋃ j, G j '' convexHull ℝ (range (d j))) ∪ ⋃ i, (B i).carrier) ∪
        T.toPlaneComplex.support := by
    simp only [A, C, c, iUnion_sum, Sum.elim_inl, Sum.elim_inr,
      OpenPartialHomeomorph.refl_apply, image_id]
    rw [hcover, hbands, meshTriangleBasis_sources_cover, union_assoc]
  let _ := Fintype.ofFinite A
  let index := Fintype.equivFin A
  refine ⟨Fintype.card A, C ∘ index.symm, c ∘ index.symm,
    fun p => hC _, fun p => hCi _, fun p => hCsource _, ?_, ?_⟩
  · intro p q hpq
    exact hparents _ _ (fun h => hpq (index.symm.injective h))
  · rw [← htotal]
    ext x
    constructor
    · rintro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨index.symm p, hp⟩
    · rintro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨index p, ?_⟩
      simpa only [Function.comp_apply, index.symm_apply_apply] using hp

end PoincareConjecture
