import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalDiskAttachmentComplement
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleNormalCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBoundaryPolygons
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularSection

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_finitePL_annular_contact_coordinates_of_presentation
    {E X α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R S : Set X}
    (he : PLDomain e R) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F R)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite) (hGQ : G.space ⊆ Q.target)
    (hphysical : Q.symm '' G.space = S) (hSR : S ⊆ interior R)
    {A : Set E} (H : Ann ≃ₜ A) (hH : H.IsFinitePL)
    (hSA : F '' S ⊆ A)
    (hrim : ∀ z : Ann, depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1 →
      (H z : E) ∈ F '' frontier R)
    (hGpoly : HasDisjointPolygonPresentation G.space) :
    ∃ (f : V3 → P2) (C : Set P2) (q : G.space ≃ₜ C),
      FinitePiecewiseAffineOn f G.space ∧ InjOn f G.space ∧ C = f '' G.space ∧
      q.IsFinitePL ∧ (∀ x : G.space, (q x : P2) = f x) ∧
      C ⊆ {z | -1 < depth 8 z ∧ depth 8 z < 1} ∧
      HasDisjointPolygonPresentation C ∧
      (∀ x ∈ G.space, ∃ z : Ann, (z : P2) = f x ∧ (H z : E) = F (Q.symm x)) ∧
      Subtype.val '' (H '' (Subtype.val ⁻¹' C : Set Ann)) = F '' S := by
  classical
  have hgR (x : V3) (hx : x ∈ G.space) : Q.symm x ∈ interior R :=
    hSR (hphysical.subset (mem_image_of_mem Q.symm hx))
  have hQPL : PolyhedralPLInCharts e Q.symm G.space := by
    simpa only [Function.comp_id] using polyhedralPLInCharts_of_compatible_inverse e Q
      (fun y _ => he.cover y) hQ G hG (f:=id)
      ⟨G,hG,rfl,G.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)⟩ hGQ
  have hfF : FinitePiecewiseAffineOn (F ∘ Q.symm) G.space :=
    hQPL.finitePiecewiseAffineOn_comp G hG hF
  have hmapA : MapsTo (F ∘ Q.symm) G.space A := by
    intro x hx
    exact hSA ⟨Q.symm x,hphysical.subset ⟨x,hx,rfl⟩,rfl⟩
  obtain ⟨j,hj,hjval⟩ := hH.symm
  let f := j ∘ (F ∘ Q.symm)
  have hf : FinitePiecewiseAffineOn f G.space := hj.comp hfF hmapA
  have hfval (x : G.space) : f x = (H.symm ⟨F (Q.symm x),hmapA x.property⟩ : P2) :=
    (hjval ⟨F (Q.symm x),hmapA x.property⟩).symm
  have hfi : InjOn f G.space := by
    intro x hx y hy hxy
    have heq : H.symm ⟨F (Q.symm x),hmapA hx⟩ =
        H.symm ⟨F (Q.symm y),hmapA hy⟩ :=
      Subtype.ext ((hfval ⟨x,hx⟩).symm.trans (hxy.trans (hfval ⟨y,hy⟩)))
    have hFxy := congrArg Subtype.val (H.symm.injective heq)
    exact Q.symm.injOn (hGQ hx) (hGQ hy)
      (hFi (interior_subset (hgR x hx)) (interior_subset (hgR y hy)) hFxy)
  let C := f '' G.space
  let fc : G.space → C := fun x => ⟨f x,mem_image_of_mem f x.property⟩
  have hfc : Continuous fc := hf.continuousOn.domRestrict.subtype_mk _
  have hbij : Function.Bijective fc := by
    constructor
    · intro x y hh
      exact Subtype.ext (hfi x.property y.property (congrArg Subtype.val hh))
    · rintro ⟨y,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  let : CompactSpace G.space := isCompact_iff_compactSpace.mp (G.isCompact_space_of_finite hG)
  let q : G.space ≃ₜ C := Continuous.homeoOfEquivCompactToT2
    (f:=Equiv.ofBijective fc hbij) hfc
  have hq : q.IsFinitePL := ⟨f,hf,fun _ => rfl⟩
  have hCdepth : C ⊆ {z | -1 < depth 8 z ∧ depth 8 z < 1} := by
    rintro _ ⟨x,hx,rfl⟩
    let z : Ann := H.symm ⟨F (Q.symm x),hmapA hx⟩
    have hzF : (H z : E) = F (Q.symm x) :=
      congrArg Subtype.val (H.apply_symm_apply _)
    have hzdepth := mem_squareAnnulus_iff_depth.mp z.property
    have hzne : depth 8 (z : P2) ≠ -1 ∧ depth 8 (z : P2) ≠ 1 := by
      constructor <;> intro hn
      all_goals
        have hzrim := hrim z (by tauto)
        rw [hzF] at hzrim
        obtain ⟨y,hy,hyeq⟩ := hzrim
        have hyR : y ∈ R := he.closed.closure_subset (frontier_subset_closure hy)
        have hxy := hFi hyR (interior_subset (hgR x hx)) hyeq
        have hyint : y ∈ interior R := hxy.symm ▸ hgR x hx
        exact hy.2 hyint
    rw [hfval ⟨x,hx⟩]
    exact ⟨lt_of_le_of_ne hzdepth.1 (Ne.symm hzne.1),lt_of_le_of_ne hzdepth.2 hzne.2⟩
  refine ⟨f,C,q,hf,hfi,rfl,hq,fun _ => rfl,hCdepth,hGpoly.of_finitePL q hq,?_,?_⟩
  · intro x hx
    exact ⟨H.symm ⟨F (Q.symm x),hmapA hx⟩,(hfval ⟨x,hx⟩).symm,
      congrArg Subtype.val (H.apply_symm_apply _)⟩
  · ext y
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      obtain ⟨x,hx,hxz⟩ := hz
      have hz' : z = H.symm ⟨F (Q.symm x),hmapA hx⟩ :=
        Subtype.ext (hxz.symm.trans (hfval ⟨x,hx⟩))
      rw [hz']
      exact ⟨Q.symm x,hphysical.subset ⟨x,hx,rfl⟩,
        (congrArg Subtype.val (H.apply_symm_apply ⟨F (Q.symm x),hmapA hx⟩)).symm⟩
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨z,hz,rfl⟩ := hphysical.symm.subset hx
      let a : Ann := H.symm ⟨F (Q.symm z),hmapA hz⟩
      refine ⟨H a,⟨a,?_,rfl⟩,congrArg Subtype.val (H.apply_symm_apply _)⟩
      exact ⟨z,hz,hfval ⟨z,hz⟩⟩

theorem HamiltonMarkedProtectedBall.exists_original_annular_contact_coordinates_of_presentation
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite) (hGQ : G.space ⊆ Q.target)
    (hphysical : Q.symm '' G.space = S)
    (hS : S ⊆ frontier D ∩ interior (latticeHandleDomain ι κ L))
    (hGpoly : HasDisjointPolygonPresentation G.space) :
    ∃ (s : Finset (latticeHandleDomain ι κ L))
      (F : LatticeHandleAmbient ι κ L → (s → ℝ × V3))
      (K J B : SimplicialComplex ℝ (s → ℝ × V3))
      (H : latticeHandleDomain ι κ L ≃ₜ K.space)
      (g : (s → ℝ × V3) → latticeHandleDomain ι κ L)
      (ann : Ann ≃ₜ (F '' frontier D \ (J.space \ B.space) : Set (s → ℝ × V3)))
      (f : V3 → P2) (C : Set P2) (q : G.space ≃ₜ C),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F (latticeHandleDomain ι κ L) ∧ K.faces.Finite ∧
      K.space = F '' latticeHandleDomain ι κ L ∧
      (∀ x, (H x : s → ℝ × V3) = F x) ∧ ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : LatticeHandleAmbient ι κ L) = (H.symm z : LatticeHandleAmbient ι κ L)) ∧
      PolyhedralPLInCharts e (fun z => (g z : LatticeHandleAmbient ι κ L)) K.space ∧
      J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2) ∧
      B.space = F '' (hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) ∧
      ann.IsFinitePL ∧
      (∀ z : Ann, (ann z : s → ℝ × V3) ∈ J.space ↔
        depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) ∧
      FinitePiecewiseAffineOn f G.space ∧ InjOn f G.space ∧ C = f '' G.space ∧
      q.IsFinitePL ∧ (∀ x : G.space, (q x : P2) = f x) ∧
      C ⊆ {z | -1 < depth 8 z ∧ depth 8 z < 1} ∧
      HasDisjointPolygonPresentation C ∧
      (∀ x ∈ G.space, ∃ z : Ann, (z : P2) = f x ∧ (ann z : s → ℝ × V3) = F (Q.symm x)) ∧
      Subtype.val '' (ann '' (Subtype.val ⁻¹' C : Set Ann)) = F '' S := by
  classical
  obtain ⟨hι⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hi
  let : Unique ι := hι
  obtain ⟨s,F,K,J,B,H,g,d,r,ann,col,hFc,hF,hFi,hK,hKs,hH,hgc,hg,hgPL,
    hball,hJK,hBJ,hJ,hB,hJmark,hBmark,hd,hdis,hcover,hrcover,hann,hlo,hhi,_⟩ :=
    b.exists_original_disk_complement_model he (by omega)
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hSA : F '' S ⊆ F '' frontier D \ (J.space \ B.space) := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨mem_image_of_mem F (hS hx).1,?_⟩
    rintro ⟨hxJ,_⟩
    rw [hJmark,←hmark] at hxJ
    obtain ⟨y,hy,hxy⟩ := hxJ
    have hyeq := hFi (b.subset_domain hy.1) (interior_subset (hS hx).2) hxy
    exact hy.2.2 (hyeq.symm ▸ (hS hx).2)
  have hannboundary (z : Ann) : (ann z : s → ℝ × V3) ∈ J.space ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1 := by
    constructor
    · intro hzJ
      have hzB : (ann z : s → ℝ × V3) ∈ B.space := by
        by_contra hn
        exact (ann z).property.2 ⟨hzJ,hn⟩
      exact (hrcover.symm.subset hzB).elim
        (fun h => Or.inl ((hlo z).mpr h)) (fun h => Or.inr ((hhi z).mpr h))
    · intro hz
      exact SimplicialComplex.space_subset_of_le hBJ (hrcover.subset
        (hz.elim (fun h => Or.inl ((hlo z).mp h)) (fun h => Or.inr ((hhi z).mp h))))
  have hrim (z : Ann) (hz : depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) :
      (ann z : s → ℝ × V3) ∈ F '' frontier (latticeHandleDomain ι κ L) := by
    have hzB : (ann z : s → ℝ × V3) ∈ B.space :=
      hrcover.subset (hz.elim (fun h => Or.inl ((hlo z).mp h))
        (fun h => Or.inr ((hhi z).mp h)))
    have hzJ := SimplicialComplex.space_subset_of_le hBJ hzB
    have hzJ' : (ann z : s → ℝ × V3) ∈ F '' (D ∩ frontier (latticeHandleDomain ι κ L)) :=
      (hJmark.trans (congrArg (fun U => F '' U) hmark.symm)).subset hzJ
    exact (image_mono inter_subset_right) hzJ'
  obtain ⟨f,C,q,hf,hfi,hC,hq,hqval,hdepth,hpoly,hval,himage⟩ :=
    exists_finitePL_annular_contact_coordinates_of_presentation he F hF hFi Q hQ G hG hGQ hphysical
      (hS.trans inter_subset_right) ann hann hSA hrim hGpoly
  exact ⟨s,F,K,J,B,H,g,ann,f,C,q,hFc,hF,hFi,hK,hKs,hH,hgc,hg,hgPL,hJmark,hBmark,
    hann,hannboundary,hf,hfi,hC,hq,hqval,hdepth,hpoly,hval,himage⟩

theorem exists_finitePL_annular_contact_coordinates
    {E X α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R S : Set X}
    (he : PLDomain e R) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F R)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite) (hGQ : G.space ⊆ Q.target)
    (hphysical : Q.symm '' G.space = S) (hSR : S ⊆ interior R)
    {A : Set E} (H : Ann ≃ₜ A) (hH : H.IsFinitePL)
    (hSA : F '' S ⊆ A)
    (hrim : ∀ z : Ann, depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1 →
      (H z : E) ∈ F '' frontier R)
    (hGc : ∀ a ∈ G.faces, a.card ≤ 2)
    (hdegree : ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) :
    ∃ (f : V3 → P2) (C : Set P2) (q : G.space ≃ₜ C),
      FinitePiecewiseAffineOn f G.space ∧ InjOn f G.space ∧ C = f '' G.space ∧
      q.IsFinitePL ∧ (∀ x : G.space, (q x : P2) = f x) ∧
      C ⊆ {z | -1 < depth 8 z ∧ depth 8 z < 1} ∧
      HasDisjointPolygonPresentation C ∧
      (∀ x ∈ G.space, ∃ z : Ann, (z : P2) = f x ∧ (H z : E) = F (Q.symm x)) ∧
      Subtype.val '' (H '' (Subtype.val ⁻¹' C : Set Ann)) = F '' S := by
  classical
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  have hcarrier := G.actual_edgeGraph_segmentCarrier_eq_space hGc
    (fun p => Set.nonempty_of_ncard_ne_zero (by rw [hdegree p]; omega))
  obtain ⟨n,P,hP,hunion,hdis⟩ :=
    G.vertexAbstractComplex.edgeGraph.exists_component_polygons_of_two_neighbors
      ((↑) : G.vertices → V3) hdegree Subtype.val_injective
      (fun {_ _ _ _} hvw hab => G.actual_edgeGraph_segment_intersection hvw hab)
  have hGpoly : HasDisjointPolygonPresentation G.space :=
    hasDisjointPolygonPresentation_of_family n P (fun i => ⟨(hP i).1,(hP i).2.1⟩)
      (hcarrier.symm.trans hunion) hdis
  exact exists_finitePL_annular_contact_coordinates_of_presentation he F hF hFi Q hQ G hG hGQ
    hphysical hSR H hH hSA hrim hGpoly

theorem HamiltonMarkedProtectedBall.exists_original_annular_contact_coordinates
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite) (hGQ : G.space ⊆ Q.target)
    (hphysical : Q.symm '' G.space = S)
    (hS : S ⊆ frontier D ∩ interior (latticeHandleDomain ι κ L))
    (hGc : ∀ a ∈ G.faces, a.card ≤ 2)
    (hdegree : ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) :
    ∃ (s : Finset (latticeHandleDomain ι κ L))
      (F : LatticeHandleAmbient ι κ L → (s → ℝ × V3))
      (K J B : SimplicialComplex ℝ (s → ℝ × V3))
      (H : latticeHandleDomain ι κ L ≃ₜ K.space)
      (g : (s → ℝ × V3) → latticeHandleDomain ι κ L)
      (ann : Ann ≃ₜ (F '' frontier D \ (J.space \ B.space) : Set (s → ℝ × V3)))
      (f : V3 → P2) (C : Set P2) (q : G.space ≃ₜ C),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F (latticeHandleDomain ι κ L) ∧ K.faces.Finite ∧
      K.space = F '' latticeHandleDomain ι κ L ∧
      (∀ x, (H x : s → ℝ × V3) = F x) ∧ ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : LatticeHandleAmbient ι κ L) = (H.symm z : LatticeHandleAmbient ι κ L)) ∧
      PolyhedralPLInCharts e (fun z => (g z : LatticeHandleAmbient ι κ L)) K.space ∧
      J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2) ∧
      B.space = F '' (hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) ∧
      ann.IsFinitePL ∧
      (∀ z : Ann, (ann z : s → ℝ × V3) ∈ J.space ↔
        depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) ∧
      FinitePiecewiseAffineOn f G.space ∧ InjOn f G.space ∧ C = f '' G.space ∧
      q.IsFinitePL ∧ (∀ x : G.space, (q x : P2) = f x) ∧
      C ⊆ {z | -1 < depth 8 z ∧ depth 8 z < 1} ∧
      HasDisjointPolygonPresentation C ∧
      (∀ x ∈ G.space, ∃ z : Ann, (z : P2) = f x ∧ (ann z : s → ℝ × V3) = F (Q.symm x)) ∧
      Subtype.val '' (ann '' (Subtype.val ⁻¹' C : Set Ann)) = F '' S := by
  classical
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  have hcarrier := G.actual_edgeGraph_segmentCarrier_eq_space hGc
    (fun p => Set.nonempty_of_ncard_ne_zero (by rw [hdegree p]; omega))
  obtain ⟨n,P,hP,hunion,hdis⟩ :=
    G.vertexAbstractComplex.edgeGraph.exists_component_polygons_of_two_neighbors
      ((↑) : G.vertices → V3) hdegree Subtype.val_injective
      (fun {_ _ _ _} hvw hab => G.actual_edgeGraph_segment_intersection hvw hab)
  have hGpoly : HasDisjointPolygonPresentation G.space :=
    hasDisjointPolygonPresentation_of_family n P (fun i => ⟨(hP i).1,(hP i).2.1⟩)
      (hcarrier.symm.trans hunion) hdis
  exact b.exists_original_annular_contact_coordinates_of_presentation he hdim hi Q hQ G hG
    hGQ hphysical hS hGpoly

end PoincareConjecture.M76
