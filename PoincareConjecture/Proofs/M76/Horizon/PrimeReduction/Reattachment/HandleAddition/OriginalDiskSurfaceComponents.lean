import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalInteriorSliceCrossing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalBoundarySliceCrossing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorSurfaceModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.Model

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ×ℝ)×ℝ)
local notation "P2" => (ℝ×ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalDiskProduct.exists_regular_surface_contact_components
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (he : PLDomain e R)
    (hcover : ∀x∈S,∃i,x∈(e i).source)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (D2×ˢIoo (-1:ℝ) 1))))
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    {p : P2→X} (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space=S∩R)
    (hcross : ∀x∈S∩frontier R,∃Q:OpenPartialHomeomorph X V3,
      x∈Q.source ∧ Q x=0 ∧
      (∀i,(e i).symm.trans Q∈piecewiseAffineGroupoid V3) ∧
      (∀y∈Q.source,y∈S ↔ Q y 1=0) ∧
      ∀y∈Q.source,y∈frontier R ↔ Q y 0=0) :
    ∃t:I,(t:ℝ)∈Ioo (-(1/2):ℝ) (1/2) ∧
      (∀y∈S∩frontier R,y∈P.slice t '' D2 →
        ∃C:OriginalSurfacePairChart e (S∩R) (P.slice t '' D2) y true,
          (∀v∈C.coordinates.source,C.chart.symm v∈R ↔ 0≤(C.coordinates v).1.2) ∧
          ∀v∈C.coordinates.source,C.chart.symm v∈frontier R ↔ (C.coordinates v).1.2=0) ∧
      (∀y∈S∩interior R,y∈P.slice t '' D2 →
        Nonempty (OriginalSurfacePairChart e (S∩R) (P.slice t '' D2) y false)) ∧
      Nonempty (SurfaceIntersectionComponents K.space D2 p (P.slice t) Q2) := by
  classical
  obtain ⟨Wi,hWi,hinterior⟩ := P.exists_regular_interior_crossing_heights
    s he.compatible hcover hopen
  obtain ⟨Wb,hWb,hboundary⟩ := P.exists_regular_boundary_crossing_heights
    s he hopen hcross
  obtain ⟨t,ht,htW⟩ := (Ioo_infinite (by norm_num : (-(1/2):ℝ)<1/2)).exists_notMem_finite
    (hWi.union hWb)
  have htI : t∈I := by constructor <;> linarith [ht.1,ht.2]
  have htband : t∈Icc (-(1/2):ℝ) (1/2) := Ioo_subset_Icc_self ht
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := isFinitePLBallPair_unit_cube (ι:=Fin 2)
  have hPL : PolyhedralPLInCharts e (P.slice t) L.space := hLs.symm ▸ P.polyhedral_slice htI
  have hLi : InjOn (P.slice t) L.space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val ((P.embedding_slice htI).injective
      (a₁:=⟨x,hLs.subset hx⟩) (a₂:=⟨y,hLs.subset hy⟩) hxy)
  have hbc : ∀y∈L.space∩Q2,P.slice t y∈p '' K.space →
      Nonempty (OriginalSurfacePairChart e (p '' K.space) (P.slice t '' L.space)
        (P.slice t y) true) := by
    intro y hy hyP
    have hyD := hLs.subset hy.1
    have hyS := (hps.subset hyP).1
    have hyfront := (P.slice_proper htI ⟨y,hyD⟩).mpr hy.2
    obtain ⟨C,_,_⟩ := hboundary t htband (fun h => htW (Or.inr h))
      (P.slice t y) ⟨hyS,hyfront⟩ ⟨y,hyD,rfl⟩
    simpa only [hps,hLs] using (show Nonempty (OriginalSurfacePairChart e (S∩R)
      (P.slice t '' D2) (P.slice t y) true) from ⟨C⟩)
  have hic : ∀y∈L.space\Q2,P.slice t y∈p '' K.space →
      Nonempty (OriginalSurfacePairChart e (p '' K.space) (P.slice t '' L.space)
        (P.slice t y) false) := by
    intro y hy hyP
    have hyD := hLs.subset hy.1
    have hyS := (hps.subset hyP).1
    have hyR := P.slice_inside htI hyD
    have hyint : P.slice t y∈interior R :=
      (mem_interior_iff_notMem_frontier hyR).mpr
        (fun h => hy.2 ((P.slice_proper htI ⟨y,hyD⟩).mp h))
    have hh := hinterior t htband (fun h => htW (Or.inl h))
      (P.slice t y) ⟨hyS,hyint⟩ ⟨y,hyD,rfl⟩
    simpa only [hps,hLs] using hh
  have hh := nonempty_surface_intersection_components he.compatible K L hK hL
    hp hPL hpi hLi Q2 hbc hic
  exact ⟨⟨t,htI⟩,ht,hboundary t htband (fun h => htW (Or.inr h)),
    hinterior t htband (fun h => htW (Or.inl h)),by simpa only [hLs] using hh⟩

theorem HamiltonMarkedProtectedBall.exists_replacement_exterior_essential_disk_components
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι+Fintype.card κ=3) (hi : Fintype.card ι=1)
    (e' : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (heR : PLDomain e' (latticeHandleDomain ι κ L))
    (heE : PLDomain e' (closure (latticeHandleDomain ι κ L\D)))
    (s : ChartwisePLSphere e' S) (hSR : S⊆interior (latticeHandleDomain ι κ L))
    (hcross : ∀x∈S∩frontier (closure (latticeHandleDomain ι κ L\D)),
      ∃Q:OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
        x∈Q.source ∧ Q x=0 ∧
        (∀i,(e' i).symm.trans Q∈piecewiseAffineGroupoid V3) ∧
        (∀y∈Q.source,y∈S ↔ Q y 1=0) ∧
        ∀y∈Q.source,y∈frontier (closure (latticeHandleDomain ι κ L\D)) ↔ Q y 0=0) :
    let E := closure (latticeHandleDomain ι κ L\D)
    S⊆E ∨ ∃ (K B:SimplicialComplex ℝ P2) (p:P2→LatticeHandleAmbient ι κ L)
      (j:V2→LatticeHandleAmbient ι κ L) (P:OriginalDiskProduct e' E j) (t:I),
      K.faces.Finite ∧ B≤K ∧
      PolyhedralPLInCharts e' p K.space ∧ InjOn p K.space ∧
      p '' K.space=S∩E ∧ p '' B.space=S∩frontier E ∧
      (∀z∈K.space,p z∈frontier E ↔ z∈B.space) ∧
      (∀u∈B.faces,u.card≤2) ∧ HasDisjointPolygonPresentation B.space ∧
      (t:ℝ)∈Ioo (-(1/2):ℝ) (1/2) ∧
      PolyhedralPLInCharts e' (P.slice t) D2 ∧
      Topology.IsEmbedding (fun x:D2 => P.slice t x) ∧ MapsTo (P.slice t) D2 E ∧
      (∀x:D2,P.slice t x∈frontier E ↔ x.val∈Q2) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (Dehn.squareRimLoop.map (P.rimSlice t).continuous))≠1 ∧
      (¬∃F:C(D2,frontier E),∀x:Q2,
        F ⟨x,sphere_subset_closedBall x.property⟩=P.rimSlice t x) ∧
      (∀y∈S∩frontier E,y∈P.slice t '' D2 →
        ∃C:OriginalSurfacePairChart e' (S∩E) (P.slice t '' D2) y true,
          (∀v∈C.coordinates.source,C.chart.symm v∈E ↔ 0≤(C.coordinates v).1.2) ∧
          ∀v∈C.coordinates.source,C.chart.symm v∈frontier E ↔ (C.coordinates v).1.2=0) ∧
      (∀y∈S∩interior E,y∈P.slice t '' D2 →
        Nonempty (OriginalSurfacePairChart e' (S∩E) (P.slice t '' D2) y false)) ∧
      Nonempty (SurfaceIntersectionComponents K.space D2 p (P.slice t) Q2) := by
  dsimp only
  have hEc := (b.closed_complement_geometry he hdim hi).1
  have hEne := (b.isConnected_closed_complement he hdim hi).nonempty
  rcases s.exists_planar_exterior_surface_or_subset (isCompact_latticeHandleDomain ι κ L)
    heR hSR hEc heE hEne hcross with hsub | hmodel
  · exact Or.inl hsub
  · obtain ⟨K,B,p,hK,hBK,hp,hpi,hps,hpb,hproper,_,_,hBdim,_,_,hBpoly⟩ := hmodel
    obtain ⟨j,P,hopen,hall⟩ :=
      b.exists_replacement_exterior_essential_disk_product he hdim hi e' heE
    obtain ⟨t,ht,hboundary,hinterior,hcomponents⟩ := P.exists_regular_surface_contact_components s heE
      (fun x _ => heE.cover x) (hopen 1 (by norm_num) le_rfl).1 K hK hp hpi hps hcross
    obtain ⟨hPL,hemb,hinto,hproper',hess,hnoext⟩ := hall t
    exact Or.inr ⟨K,B,p,j,P,t,hK,hBK,hp,hpi,hps,hpb,hproper,hBdim,hBpoly,
      ht,hPL,hemb,hinto,hproper',hess,hnoext,hboundary,hinterior,hcomponents⟩

end PoincareConjecture.M76
