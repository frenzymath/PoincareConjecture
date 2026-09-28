import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialDiskCircleMinimum










set_option autoImplicit false
open Set Geometry Topology
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem exists_innermost_compression_circle_with_surface_rim
    {X : Type*} {J K B : Set P2} {f g : P2 → X}
    (hJ : Convex ℝ J)
    (C : SurfaceIntersectionComponents J K f g B)
    (M : SurfaceIntersectionComponents K J g f (frontier J))
    (hrims : ∀ x ∈ J,∀ y ∈ K,f x = g y → (x ∈ frontier J ↔ y ∈ B))
    (hcircle : ∃ i,Disjoint (M.pieces i) (frontier J)) :
    ∃ i j,∃ (n m : ℕ) (P : Polygon P2 (n+3)) (Q : Polygon P2 (m+3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
      Function.Injective Q ∧ Q.HasSimplicialEdges ∧
      P.boundary ℝ = C.pieces i ∧ Q.boundary ℝ = M.pieces j ∧
      P.boundary ℝ ⊆ K \ B ∧
      IsFinitePLBallPair P2 (closure Q.inside) (Q.boundary ℝ) ∧
      closure Q.inside ⊆ interior J ∧
      g '' P.boundary ℝ = f '' Q.boundary ℝ ∧
      closure Q.inside ∩ (J ∩ f ⁻¹' (g '' K)) = Q.boundary ℝ ∧
      Disjoint Q.inside (J ∩ f ⁻¹' (g '' K)) := by
  classical
  let := C.components_finite
  let := M.components_finite
  have hCsub (i) : C.pieces i ⊆ K := fun x hx =>
    (C.right_space.subset (C.cover.symm.subset (mem_iUnion.mpr ⟨i,hx⟩))).1
  have hMsub (i) : M.pieces i ⊆ J := fun x hx =>
    (M.right_space.subset (M.cover.symm.subset (mem_iUnion.mpr ⟨i,hx⟩))).1
  have hMcover : (⋃ i,M.pieces i) = J ∩ f ⁻¹' (g '' K) :=
    M.cover.symm.trans M.right_space
  have hgood : ∃ i,∃ (n : ℕ) (P : Polygon P2 (n+3)),Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = M.pieces i ∧ closure P.inside ⊆ interior J := by
    obtain ⟨i,hi⟩ := hcircle
    rcases M.models i with ha | ⟨n,P,hPi,hP,hPb,_⟩
    · obtain ⟨u,v,_,huv⟩ := ha.exists_boundary_eq_pair
      have hu := huv.symm.subset (show u∈({u,v}:Set P2) from Or.inl rfl)
      exact (disjoint_left.mp hi hu.1 hu.2).elim
    · refine ⟨i,n,P,hPi,hP,hPb,P.closure_inside_subset_convex hP hPi hJ.interior ?_⟩
      rintro _ ⟨v,rfl⟩
      have hv := hPb.subset (mem_iUnion.mpr ⟨v,left_mem_affineSegment ℝ _ _⟩)
      exact (mem_interior_iff_notMem_frontier (hMsub i hv)).mpr
        (fun hf => disjoint_left.mp hi hv hf)
  obtain ⟨j,m,Q,hQi,hQ,hQb,hQball,hQin,hQinter,hQavoid⟩ :=
    exists_innermost_region_disk_of_mixed_contacts M.pieces M.disjoint
      (Rim := frontier J) (U := interior J)
      (disjoint_left.mpr fun _ hx hy => hx.2 hy) M.models hgood
  have hclosedM : Disjoint (M.pieces j) (frontier J) := by
    apply disjoint_left.mpr
    intro x hx hxf
    exact hxf.2 (hQin (hQball.1 (hQb.symm.subset hx)))
  obtain ⟨c,hc⟩ := M.exists_component_equiv C
  let i := c.symm j
  have hphysical : g '' C.pieces i = f '' Q.boundary ℝ := by
    rw [hc,hQb]
    simp only [i,c.apply_symm_apply]
  have hclosedC : Disjoint (C.pieces i) B := by
    apply disjoint_left.mpr
    intro x hx hxB
    obtain ⟨y,hy,hyx⟩ := hphysical.subset ⟨x,hx,rfl⟩
    have hyM := hQb.subset hy
    exact disjoint_left.mp hclosedM hyM
      ((hrims y (hMsub j hyM) x (hCsub i hx) hyx).mpr hxB)
  have hPmodel : ∃ (n : ℕ) (P : Polygon P2 (n+3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧ P.boundary ℝ = C.pieces i := by
    rcases C.models i with ha | ⟨n,P,hPi,hP,hPb,_⟩
    · obtain ⟨u,v,_,huv⟩ := ha.exists_boundary_eq_pair
      have hu := huv.symm.subset (show u∈({u,v}:Set P2) from Or.inl rfl)
      exact (disjoint_left.mp hclosedC hu.1 hu.2).elim
    · exact ⟨n,P,hPi,hP,hPb⟩
  obtain ⟨n,P,hPi,hP,hPb⟩ := hPmodel
  refine ⟨i,j,n,m,P,Q,hPi,hP,hQi,hQ,hPb,hQb,?_,hQball,hQin,?_,
    hMcover ▸ hQinter,hMcover ▸ hQavoid⟩
  · intro x hx
    have hxi := hPb.subset hx
    exact ⟨hCsub i hxi,fun hxB => disjoint_left.mp hclosedC hxi hxB⟩
  · rw [hPb]
    exact hphysical

open Classical in
theorem exists_actual_disk_at_innermost_compression_circle
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R S : Set X}
    (J : SimplicialComplex ℝ P2) (hJcv : Convex ℝ J.space)
    {K B : Set P2} {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f J.space) (hfi : InjOn f J.space)
    (hfR : MapsTo f J.space R)
    (hfproper : ∀ x ∈ J.space,f x∈frontier R ↔ x∈frontier J.space)
    (hgproper : ∀ x ∈ K,g x∈frontier R ↔ x∈B)
    (himage : g '' K = S ∩ R)
    (C : SurfaceIntersectionComponents J.space K f g B)
    (M : SurfaceIntersectionComponents K J.space g f (frontier J.space))
    (hcircle : ∃ i,Disjoint (M.pieces i) (frontier J.space)) :
    ∃ i,∃ (n m : ℕ) (P : Polygon P2 (n+3)) (Q : Polygon P2 (m+3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧ P.boundary ℝ=C.pieces i ∧
      P.boundary ℝ⊆K\B ∧ Function.Injective Q ∧ Q.HasSimplicialEdges ∧
      IsFinitePLBallPair P2 (closure Q.inside) (Q.boundary ℝ) ∧
      PolyhedralPLInCharts e f (closure Q.inside) ∧ InjOn f (closure Q.inside) ∧
      closure Q.inside ⊆ interior J.space ∧
      f '' closure Q.inside ⊆ interior R ∧
      (∀ z∈closure Q.inside,f z∈S ↔ z∈Q.boundary ℝ) ∧
      g '' P.boundary ℝ=f '' Q.boundary ℝ := by
  have hrims : ∀ x∈J.space,∀ y∈K,f x=g y → (x∈frontier J.space ↔ y∈B) := by
    intro x hx y hy hxy
    rw [←hfproper x hx,←hgproper y hy,hxy]
  obtain ⟨i,j,n,m,P,Q,hPi,hP,hQi,hQ,hPb,hQb,hPK,hball,hQin,hphys,hinter,_⟩ :=
    exists_innermost_compression_circle_with_surface_rim hJcv C M hrims hcircle
  have hQsub : closure Q.inside⊆J.space := hQin.trans interior_subset
  obtain ⟨N,hN⟩ := Q.exists_triangulation hQ hQi
  have hfQ : PolyhedralPLInCharts e f (closure Q.inside) := by
    rw [←hN.space_eq]
    exact hf.restrict_finite N hN.finite_faces (hN.space_eq.subset.trans hQsub)
  refine ⟨i,n,m,P,Q,hPi,hP,hPb,hPK,hQi,hQ,hball,hfQ,hfi.mono hQsub,hQin,?_,?_,hphys⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact (mem_interior_iff_notMem_frontier (hfR (hQsub hx))).mpr
      (fun hfr => ((hfproper x (hQsub hx)).mp hfr).2 (hQin hx))
  · intro z hz
    constructor
    · intro hzS
      exact hinter.subset ⟨hz,hQsub hz,himage.symm.subset ⟨hzS,hfR (hQsub hz)⟩⟩
    · intro hzQ
      have hh := hinter.symm.subset hzQ
      exact (himage.subset hh.2.2).1

end PoincareConjecture.M76

