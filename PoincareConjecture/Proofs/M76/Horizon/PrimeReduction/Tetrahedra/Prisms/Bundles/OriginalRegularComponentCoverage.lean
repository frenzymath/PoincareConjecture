import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalTrimmedPartitionReflection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalTetrahedralCutFamily
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartStarPurity

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)

theorem OriginalTetrahedralCutFamily.ball_subset_tetrahedron
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X}
    (F : OriginalTetrahedralCutFamily K g S) (t : K.FaceOfCard 4) (k : F.BallIndex t) :
    F.ball t k ⊆ convexHull ℝ (t.1 : Set E) :=
  fun _ hx => (F.cover t).subset (mem_iUnion.mpr ⟨k,hx⟩)

theorem OriginalTetrahedralCutFamily.mem_cut_iff_physical
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X}
    (F : OriginalTetrahedralCutFamily K g S) (hgi : InjOn g K.space)
    (t : K.FaceOfCard 4) {x : E} (hx : x ∈ convexHull ℝ (t.1 : Set E)) :
    x ∈ (⋃ i, F.cut t i) ↔ g x ∈ S :=
  original_face_cut_mem_iff K g hgi t.2.1 (iUnion_subset (F.disk_subset t)) (F.physical t) hx

theorem OriginalTetrahedralCutFamily.component_physical
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X}
    (F : OriginalTetrahedralCutFamily K g S) (hgi : InjOn g K.space)
    (t : K.FaceOfCard 4) (k : F.BallIndex t) {x : E} (hx : x ∈ F.ball t k \ g ⁻¹' S) :
    connectedComponentIn (convexHull ℝ (t.1 : Set E) \ g ⁻¹' S) x = F.ball t k \ g ⁻¹' S := by
  have hglobal : (convexHull ℝ (t.1 : Set E) \ g ⁻¹' S : Set E) =
      convexHull ℝ (t.1 : Set E) \ ⋃ i, F.cut t i := by
    ext y
    exact and_congr_right (fun hy => not_congr (F.mem_cut_iff_physical hgi t hy).symm)
  have hlocal : (F.ball t k \ g ⁻¹' S : Set E) = F.ball t k \ ⋃ i, F.cut t i := by
    ext y
    exact and_congr_right (fun hy => not_congr
      (F.mem_cut_iff_physical hgi t (F.ball_subset_tetrahedron t k hy)).symm)
  rw [hglobal,hlocal]
  exact F.component t k x (hlocal.subset hx)

theorem OriginalTetrahedralCutFamily.component_class
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X}
    (F : OriginalTetrahedralCutFamily K g S) (hgi : InjOn g K.space)
    (t : K.FaceOfCard 4) (k : F.BallIndex t)
    (x y : (K.space \ g ⁻¹' S : Set E)) (hx : (x : E) ∈ F.ball t k)
    (hy : (y : E) ∈ F.ball t k) : ConnectedComponents.mk y = ConnectedComponents.mk x :=
  original_cut_ball_component_class K g t.2.1 (F.ball_subset_tetrahedron t k)
    (fun _ hz => F.component_physical hgi t k hz)
    (show (x : E) ∈ F.ball t k \ g ⁻¹' S from ⟨hx,x.property.2⟩)
    (show (y : E) ∈ F.ball t k \ g ⁻¹' S from ⟨hy,y.property.2⟩)

theorem exists_regular_cell_of_component_not_mem_bad
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space) {S : Set X}
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (F : OriginalTetrahedralCutFamily K g S)
    (bad : Set (ConnectedComponents (K.space \ g ⁻¹' S : Set E)))
    (hbad : ∀ (s : K.FaceOfCard 3)
      (y : (convexHull ℝ (s.1 : Set E) \ ⋃ i, (D s).arc i : Set E)),
      ConnectedComponents.mk y ∈ (D s).exceptional →
      ConnectedComponents.mk
        (⟨y,(D s).cut_subset_original_complement s.2.1 hgi y.property⟩ :
          (K.space \ g ⁻¹' S : Set E)) ∈ bad)
    (x : (K.space \ g ⁻¹' S : Set E)) (hx : ConnectedComponents.mk x ∉ bad) :
    ∃ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, (x : E) ∈ F.ball j.1.1 j.1.2 := by
  obtain ⟨s,hs,hxs⟩ := SimplicialComplex.mem_space_iff.mp x.property.1
  obtain ⟨t,ht,hst,ht4⟩ := hpure s hs
  let T : K.FaceOfCard 4 := ⟨t,ht,ht4⟩
  have hxT : (x : E) ∈ convexHull ℝ (T.1 : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr hst) hxs
  obtain ⟨k,hxk⟩ := mem_iUnion.mp ((F.cover T).symm.subset hxT)
  have hregular : ∀ (f : TetrahedronFace K T.1)
      (y : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f.1).arc i : Set E)),
      (y : E) ∈ F.ball T k → ConnectedComponents.mk y ∉ (D f.1).exceptional := by
    intro f y hy hbadY
    let y' : (K.space \ g ⁻¹' S : Set E) :=
      ⟨y,(D f.1).cut_subset_original_complement f.1.2.1 hgi y.property⟩
    have hclass := F.component_class hgi T k x y' hxk hy
    exact hx (hclass ▸ hbad f.1 y hbadY)
  exact ⟨⟨⟨T,k⟩,hregular⟩,hxk⟩

theorem nonexceptional_component_eq_regular_cell_cores
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space) {S : Set X}
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (F : OriginalTetrahedralCutFamily K g S)
    (bad : Set (ConnectedComponents (K.space \ g ⁻¹' S : Set E)))
    (hbad : ∀ (s : K.FaceOfCard 3)
      (y : (convexHull ℝ (s.1 : Set E) \ ⋃ i, (D s).arc i : Set E)),
      ConnectedComponents.mk y ∈ (D s).exceptional →
      ConnectedComponents.mk
        (⟨y,(D s).cut_subset_original_complement s.2.1 hgi y.property⟩ :
          (K.space \ g ⁻¹' S : Set E)) ∈ bad)
    (x : (K.space \ g ⁻¹' S : Set E)) (hx : ConnectedComponents.mk x ∉ bad) :
    connectedComponentIn (K.space \ g ⁻¹' S) (x : E) =
      ⋃ j : {j : RegularOriginalCutCell K g S D F.BallIndex F.ball //
        ((F.ball j.1.1 j.1.2 \ g ⁻¹' S) ∩
          connectedComponentIn (K.space \ g ⁻¹' S) (x : E)).Nonempty},
        F.ball j.1.1.1 j.1.1.2 \ g ⁻¹' S := by
  ext y
  constructor
  · intro hy
    have hyP := connectedComponentIn_subset (K.space \ g ⁻¹' S) (x : E) hy
    have hclass := (Topology.mem_componentIn_iff_component_class x.property hyP).mp hy
    obtain ⟨j,hyj⟩ := exists_regular_cell_of_component_not_mem_bad K g hgi hpure D F bad hbad
      ⟨y,hyP⟩ (hclass.symm ▸ hx)
    exact mem_iUnion.mpr ⟨⟨j,⟨y,⟨hyj,hyP.2⟩,hy⟩⟩,⟨hyj,hyP.2⟩⟩
  · intro hy
    obtain ⟨j,hyj⟩ := mem_iUnion.mp hy
    obtain ⟨z,hzj,hzx⟩ := j.2
    have hzP := connectedComponentIn_subset (K.space \ g ⁻¹' S) (x : E) hzx
    have hyP : y ∈ K.space \ g ⁻¹' S :=
      ⟨K.convexHull_subset_space j.1.1.1.2.1
        (F.ball_subset_tetrahedron j.1.1.1 j.1.1.2 hyj.1),hyj.2⟩
    have hclass := F.component_class hgi j.1.1.1 j.1.1.2 ⟨z,hzP⟩ ⟨y,hyP⟩ hzj.1 hyj.1
    apply (Topology.mem_componentIn_iff_component_class x.property hyP).mpr
    exact hclass.trans ((Topology.mem_componentIn_iff_component_class x.property hzP).mp hzx)

theorem exists_regular_cell_of_original_chart_stars
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgi : InjOn (fun z => (g z : X)) K.space)
    (hstars : ∀ p ∈ K.vertices, ∃ Q : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space Q.source ∧
      (K.closedStar p).AffineOnFaces (fun z => Q (g z)) ∧
      (Q.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ Q.source, y ∈ R ↔ 0 ≤ ell (Q y)))
    {S : Set X}
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K (fun z => (g z : X)) S s.1)
    (F : OriginalTetrahedralCutFamily K (fun z => (g z : X)) S)
    (bad : Set (ConnectedComponents (K.space \ (fun z => (g z : X)) ⁻¹' S : Set E)))
    (hbad : ∀ (s : K.FaceOfCard 3)
      (y : (convexHull ℝ (s.1 : Set E) \ ⋃ i, (D s).arc i : Set E)),
      ConnectedComponents.mk y ∈ (D s).exceptional →
      ConnectedComponents.mk
        (⟨y,(D s).cut_subset_original_complement s.2.1 hgi y.property⟩ :
          (K.space \ (fun z => (g z : X)) ⁻¹' S : Set E)) ∈ bad)
    (x : (K.space \ (fun z => (g z : X)) ⁻¹' S : Set E))
    (hx : ConnectedComponents.mk x ∉ bad) :
    ∃ j : RegularOriginalCutCell K (fun z => (g z : X)) S D F.BallIndex F.ball,
      (x : E) ∈ F.ball j.1.1 j.1.2 :=
  exists_regular_cell_of_component_not_mem_bad K (fun z => (g z : X)) hgi
    (exists_tetrahedral_coface_of_original_chart_stars K hK H g hg hstars) D F bad hbad x hx

end PoincareConjecture.M76.PrismBelt
