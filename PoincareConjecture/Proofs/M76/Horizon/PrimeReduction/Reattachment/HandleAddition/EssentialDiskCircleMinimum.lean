import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialDiskCircleReduction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.DiskContactSourceCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.BoundaryPairChartAgreement

set_option autoImplicit false
open Set Metric Geometry Topology
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

open Classical in
theorem exists_surface_components_without_inessential_circle_of_minimal_disk
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) {B : Set P2}
    {g : P2 → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hgR : MapsTo g K.space R)
    (hgproper : ∀ x ∈ K.space,g x ∈ frontier R ↔ x ∈ B)
    (f : V2 → X)
    (hf : PolyhedralPLInCharts e f D2)
    (hfi : IsEmbedding (fun x : D2 => f x))
    (hfR : MapsTo f D2 R)
    (hfproper : ∀ x : D2,f x ∈ frontier R ↔ (x : V2) ∈ Q2)
    (hfno : ¬ ∃ F : C(D2,frontier R),∀ x : Q2,
      (F ⟨x,sphere_subset_closedBall x.property⟩ : X) = f x)
    (hboundary : ∀ y ∈ (g '' K.space) ∩ frontier R,y ∈ f '' D2 →
      ∃ C : OriginalSurfacePairChart e (g '' K.space) (f '' D2) y true,
        (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔ 0 ≤ (C.coordinates v).1.2) ∧
        ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔ (C.coordinates v).1.2 = 0)
    (hinterior : ∀ y ∈ (g '' K.space) ∩ interior R,y ∈ f '' D2 →
      Nonempty (OriginalSurfacePairChart e (g '' K.space) (f '' D2) y false))
    (hminimum : ∀ k : V2 → X,
      PolyhedralPLInCharts e k D2 → IsEmbedding (fun x : D2 => k x) →
      MapsTo k D2 R → (∀ x : D2,k x ∈ frontier R ↔ (x : V2) ∈ Q2) →
      (¬ ∃ F : C(D2,frontier R),∀ x : Q2,
        (F ⟨x,sphere_subset_closedBall x.property⟩ : X) = k x) →
      (∀ y ∈ (g '' K.space) ∩ frontier R,y ∈ k '' D2 →
        ∃ C : OriginalSurfacePairChart e (g '' K.space) (k '' D2) y true,
          (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔ 0 ≤ (C.coordinates v).1.2) ∧
          ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔ (C.coordinates v).1.2 = 0) →
      (∀ y ∈ (g '' K.space) ∩ interior R,y ∈ k '' D2 →
        Nonempty (OriginalSurfacePairChart e (g '' K.space) (k '' D2) y false)) →
      Nat.card (ConnectedComponents (D2 ∩ f ⁻¹' (g '' K.space) : Set V2)) ≤
        Nat.card (ConnectedComponents (D2 ∩ k ⁻¹' (g '' K.space) : Set V2))) :
    let a := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
    ∃ (J : SimplicialComplex ℝ P2), J.faces.Finite ∧ J.space = a '' D2 ∧
      ∃ C : SurfaceIntersectionComponents J.space K.space (f ∘ a.symm) g B,
        (¬ ∃ i, ∃ (n : ℕ) (P : Polygon P2 (n+3)), Function.Injective P ∧
          P.HasSimplicialEdges ∧ P.boundary ℝ = C.pieces i ∧
          closure P.inside ⊆ interior K.space \ B) ∧
        Nonempty (SurfaceIntersectionComponents K.space J.space g (f ∘ a.symm) (frontier J.space)) := by
  classical
  intro a
  have hball := (isFinitePLBallPair_unit_cube (ι := Fin 2)).affine_image
    a.toContinuousLinearMap.toContinuousAffineMap a.injective.injOn
  obtain ⟨_,_,_,_,_,_,⟨_,⟨J,hJ,hJs,_⟩,_⟩,_⟩ := hball
  change J.space = a '' D2 at hJs
  have hJcv : Convex ℝ J.space := hJs.symm ▸
    (convex_closedBall (0 : V2) 1).linear_image a.toLinearMap
  have hJfront : frontier J.space = a '' Q2 := by
    rw [hJs]
    change frontier (a.toHomeomorph '' D2) = a.toHomeomorph '' Q2
    rw [←a.toHomeomorph.image_frontier,frontier_closedBall _ (by norm_num : (1:ℝ)≠0)]
  have hback (x : P2) (hx : x ∈ J.space) : a.symm x ∈ D2 := by
    obtain ⟨y,hy,rfl⟩ := hJs.subset hx
    simpa using hy
  have hforward (x : V2) (hx : x ∈ D2) : a x ∈ J.space :=
    hJs.symm.subset (mem_image_of_mem a hx)
  have hbackfront (x : P2) : x ∈ frontier J.space ↔ a.symm x ∈ Q2 := by
    rw [hJfront]
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
    · intro hx
      exact ⟨a.symm x,hx,a.apply_symm_apply x⟩
  let f0 : P2 → X := f ∘ a.symm
  have hf0 : PolyhedralPLInCharts e f0 J.space :=
    hf.comp_finitePiecewiseAffineOn J hJ
      ((J.affineOnFaces_affine a.symm.toContinuousLinearMap.toContinuousAffineMap).finitePiecewiseAffineOn hJ)
      hback
  have hf0i : InjOn f0 J.space := by
    intro x hx y hy hxy
    have hh := congrArg Subtype.val (hfi.injective
      (a₁ := ⟨a.symm x,hback x hx⟩) (a₂ := ⟨a.symm y,hback y hy⟩) hxy)
    exact a.symm.injective hh
  have hf0R : MapsTo f0 J.space R := fun x hx => hfR (hback x hx)
  have hf0proper : ∀ x ∈ J.space,f0 x ∈ frontier R ↔ x ∈ frontier J.space :=
    fun x hx => (hfproper ⟨a.symm x,hback x hx⟩).trans (hbackfront x).symm
  have hfimage : f0 '' J.space = f '' D2 := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨a.symm x,hback x hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨a x,hforward x hx,by simp [f0]⟩
  have hrims : ∀ x ∈ K.space,∀ y ∈ J.space,g x = f0 y →
      (x ∈ B ↔ y ∈ frontier J.space) := by
    intro x hx y hy hxy
    rw [←hgproper x hx,←hf0proper y hy,hxy]
  have hbc : ∀ y ∈ J.space ∩ frontier J.space,f0 y ∈ g '' K.space →
      Nonempty (OriginalSurfacePairChart e (g '' K.space) (f0 '' J.space) (f0 y) true) := by
    intro y hy hys
    obtain ⟨C,_,_⟩ := hboundary (f0 y) ⟨hys,(hf0proper y hy.1).mpr hy.2⟩
      (hfimage.subset (mem_image_of_mem f0 hy.1))
    simpa only [hfimage] using (show Nonempty _ from ⟨C⟩)
  have hic : ∀ y ∈ J.space \ frontier J.space,f0 y ∈ g '' K.space →
      Nonempty (OriginalSurfacePairChart e (g '' K.space) (f0 '' J.space) (f0 y) false) := by
    intro y hy hys
    have hyint : f0 y ∈ interior R :=
      (mem_interior_iff_notMem_frontier (hf0R hy.1)).mpr
        (fun hh => hy.2 ((hf0proper y hy.1).mp hh))
    have hh := hinterior (f0 y) ⟨hys,hyint⟩ (hfimage.subset (mem_image_of_mem f0 hy.1))
    simpa only [hfimage] using hh
  obtain ⟨⟨M⟩,⟨C⟩⟩ := nonempty_both_surface_intersection_components he.compatible
    K J hK hJ hg hf0 hgi hf0i B (frontier J.space) hrims hbc hic
  refine ⟨J,hJ,hJs,C,?_,⟨M⟩⟩
  intro hgood
  obtain ⟨k,hk,hki,hkR,hfix,hkproper,hsub,hkeep,hcount,⟨W,hW,hRW,hagree⟩,hcross⟩ :=
    exists_disk_contact_reduction_of_inessential_surface_circle hR he J hJ hJcv
      (K.isCompact_space_of_finite hK) hf0 hg hf0i hgi hf0R hgR hf0proper hgproper
      C M hgood hic
  let k0 : V2 → X := k ∘ a
  have hkimage : k0 '' D2 = k '' J.space := by
    rw [hJs,Set.image_image]
    rfl
  obtain ⟨_,_,_,_,_,_,⟨_,⟨J0,hJ0,hJ0s,_⟩,_⟩,_⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
  have hk0 : PolyhedralPLInCharts e k0 D2 := by
    rw [←hJ0s]
    exact hk.comp_finitePiecewiseAffineOn J0 hJ0
      ((J0.affineOnFaces_affine a.toContinuousLinearMap.toContinuousAffineMap).finitePiecewiseAffineOn hJ0)
      (fun x hx => hforward x (hJ0s.subset hx))
  let H : D2 ≃ₜ J.space := (a.toHomeomorph.image D2).trans (Homeomorph.setCongr hJs.symm)
  have hk0i : IsEmbedding (fun x : D2 => k0 x) := hki.comp H.isEmbedding
  have hk0R : MapsTo k0 D2 R := fun x hx => hkR (hforward x hx)
  have hk0proper : ∀ x : D2,k0 x ∈ frontier R ↔ (x : V2) ∈ Q2 := by
    intro x
    exact (hkproper (a x) (hforward x x.property)).trans
      ((hbackfront (a x)).trans (by simp))
  have hk0fix : EqOn k0 f Q2 := by
    intro x hx
    exact (hfix ((hbackfront (a x)).mpr (by simpa using hx))).trans (by simp [f0])
  have hk0no : ¬ ∃ F : C(D2,frontier R),∀ x : Q2,
      (F ⟨x,sphere_subset_closedBall x.property⟩ : X) = k0 x := by
    rintro ⟨F,hF⟩
    exact hfno ⟨F,fun x => (hF x).trans (hk0fix x.property)⟩
  have hk0bc : ∀ y ∈ (g '' K.space) ∩ frontier R,y ∈ k0 '' D2 →
      ∃ C : OriginalSurfacePairChart e (g '' K.space) (k0 '' D2) y true,
        (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔ 0 ≤ (C.coordinates v).1.2) ∧
        ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔ (C.coordinates v).1.2 = 0 := by
    intro y hy hyk
    have hyW := hRW hy.2
    have hyf := hfimage.subset ((hagree y hyW).mp (hkimage.subset hyk))
    obtain ⟨A,hAR,hAfr⟩ := hboundary y hy hyf
    exact A.exists_boundary_model_of_agreement hW hyW
      (fun z hz => by rw [hkimage,←hfimage]; exact hagree z hz) hAR hAfr
  have hk0ic : ∀ y ∈ (g '' K.space) ∩ interior R,y ∈ k0 '' D2 →
      Nonempty (OriginalSurfacePairChart e (g '' K.space) (k0 '' D2) y false) := by
    intro y hy hyk
    obtain ⟨x,hx,hxy⟩ := hkimage.subset hyk
    have hxnew : x ∈ J.space ∩ k ⁻¹' (g '' K.space) :=
      ⟨hx,show k x ∈ g '' K.space from hxy.symm ▸ hy.1⟩
    have hyf : y ∈ f '' D2 := hfimage.subset
      ⟨x,(hsub hxnew).1,(hkeep x hxnew).symm.trans hxy⟩
    obtain ⟨A⟩ := hinterior y hy hyf
    have hh := hcross y false ⟨hy.1,hkimage.subset hyk⟩ (hfimage.symm ▸ A)
    simpa only [hkimage] using hh
  have hmin := hminimum k0 hk0 hk0i hk0R hk0proper hk0no hk0bc hk0ic
  have hcountf := contact_component_card_source_homeomorph a.toHomeomorph D2 f (g '' K.space)
  have hcountk := contact_component_card_source_homeomorph a.toHomeomorph D2 k0 (g '' K.space)
  change Nat.card (ConnectedComponents ((a '' D2) ∩ (k0 ∘ a.symm) ⁻¹' (g '' K.space) : Set P2)) = _ at hcountk
  change Nat.card (ConnectedComponents ((a '' D2) ∩ f0 ⁻¹' (g '' K.space) : Set P2)) = _ at hcountf
  have hkcomp : k0 ∘ a.symm = k := by
    funext x
    simp [k0]
  rw [hkcomp,←hJs] at hcountk
  rw [←hJs] at hcountf
  change Nat.card (ConnectedComponents (J.space ∩ f0 ⁻¹' (g '' K.space) : Set P2)) = _ at hcountf
  rw [hcountk,hcountf] at hcount
  exact (not_lt_of_ge hmin) hcount

open Classical in
theorem HamiltonMarkedProtectedBall.exists_minimal_essential_disk_without_null_circle
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (s : ChartwisePLSphere e S)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) {B : Set P2}
    (p : P2 → LatticeHandleAmbient ι κ L)
    (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space = S ∩ closure (latticeHandleDomain ι κ L \ D))
    (hpp : ∀ x ∈ K.space,p x ∈ frontier (closure (latticeHandleDomain ι κ L \ D)) ↔ x ∈ B)
    (hcross : ∀ x ∈ S ∩ frontier (closure (latticeHandleDomain ι κ L \ D)),
      ∃ Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
        x ∈ Q.source ∧ Q x = 0 ∧
        (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ Q.source,y ∈ S ↔ Q y 1 = 0) ∧
        ∀ y ∈ Q.source,y ∈ frontier (closure (latticeHandleDomain ι κ L \ D)) ↔ Q y 0 = 0) :
    let X := LatticeHandleAmbient ι κ L
    let E := closure (latticeHandleDomain ι κ L \ D)
    let disks : Set (V2 → X) := {j |
      PolyhedralPLInCharts e j D2 ∧ IsEmbedding (fun x : D2 => j x) ∧
      MapsTo j D2 E ∧ (∀ x : D2,j x ∈ frontier E ↔ (x : V2) ∈ Q2) ∧
      (¬ ∃ F : C(D2,frontier E),∀ x : Q2,
        (F ⟨x,sphere_subset_closedBall x.property⟩ : X) = j x) ∧
      (∀ y ∈ S ∩ frontier E,y ∈ j '' D2 →
        ∃ C : OriginalSurfacePairChart e (S ∩ E) (j '' D2) y true,
          (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ E ↔ 0 ≤ (C.coordinates v).1.2) ∧
          ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier E ↔ (C.coordinates v).1.2 = 0) ∧
      ∀ y ∈ S ∩ interior E,y ∈ j '' D2 →
        Nonempty (OriginalSurfacePairChart e (S ∩ E) (j '' D2) y false)}
    let a := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
    ∃ f ∈ disks,
      (∀ k ∈ disks,Nat.card (ConnectedComponents (D2 ∩ f ⁻¹' S : Set V2)) ≤
        Nat.card (ConnectedComponents (D2 ∩ k ⁻¹' S : Set V2))) ∧
      Nonempty (SurfaceIntersectionComponents K.space D2 p f Q2) ∧
      ∃ (J : SimplicialComplex ℝ P2),J.faces.Finite ∧ J.space = a '' D2 ∧
        ∃ C : SurfaceIntersectionComponents J.space K.space (f ∘ a.symm) p B,
          (¬ ∃ i,∃ (n : ℕ) (P : Polygon P2 (n+3)),Function.Injective P ∧
            P.HasSimplicialEdges ∧ P.boundary ℝ = C.pieces i ∧
            closure P.inside ⊆ interior K.space \ B) ∧
          Nonempty (SurfaceIntersectionComponents K.space J.space p (f ∘ a.symm) (frontier J.space)) := by
  classical
  intro X E disks a
  obtain ⟨f,hf,hmin,hmodel⟩ := b.exists_minimal_essential_exterior_disk he hdim hi
    s K hK p hp hpi hps hcross
  refine ⟨f,hf,hmin,hmodel,?_⟩
  obtain ⟨hfPL,hfi,hfR,hfproper,hfno,hfbc,hfic⟩ := hf
  have hpR : MapsTo p K.space E := fun x hx => (hps.subset (mem_image_of_mem p hx)).2
  have hcontact (k : V2 → X) (hk : MapsTo k D2 E) :
      D2 ∩ k ⁻¹' (p '' K.space) = D2 ∩ k ⁻¹' S := by
    ext x
    simp only [mem_inter_iff,mem_preimage,hps]
    exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hk h.1⟩⟩
  have hbc : ∀ y ∈ (p '' K.space) ∩ frontier E,y ∈ f '' D2 →
      ∃ C : OriginalSurfacePairChart e (p '' K.space) (f '' D2) y true,
        (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ E ↔ 0 ≤ (C.coordinates v).1.2) ∧
        ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier E ↔ (C.coordinates v).1.2 = 0 := by
    intro y hy hyf
    rw [hps]
    exact hfbc y ⟨(hps.subset hy.1).1,hy.2⟩ hyf
  have hic : ∀ y ∈ (p '' K.space) ∩ interior E,y ∈ f '' D2 →
      Nonempty (OriginalSurfacePairChart e (p '' K.space) (f '' D2) y false) := by
    intro y hy hyf
    simpa only [hps] using hfic y ⟨(hps.subset hy.1).1,hy.2⟩ hyf
  apply exists_surface_components_without_inessential_circle_of_minimal_disk
    (b.closed_complement_geometry he hdim hi).1 (b.plDomain_closed_complement he hdim hi)
    K hK hp hpi hpR hpp f hfPL hfi hfR hfproper hfno hbc hic
  intro k hk hki hkR hkproper hkno hkbc hkic
  have hkb : ∀ y ∈ S ∩ frontier E,y ∈ k '' D2 →
      ∃ C : OriginalSurfacePairChart e (S ∩ E) (k '' D2) y true,
        (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ E ↔ 0 ≤ (C.coordinates v).1.2) ∧
        ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier E ↔ (C.coordinates v).1.2 = 0 := by
    intro y hy hyk
    have hyE : y ∈ E := by
      obtain ⟨x,hx,rfl⟩ := hyk
      exact hkR hx
    have hh := hkbc y ⟨hps.symm.subset ⟨hy.1,hyE⟩,hy.2⟩ hyk
    rw [hps] at hh
    exact hh
  have hki' : ∀ y ∈ S ∩ interior E,y ∈ k '' D2 →
      Nonempty (OriginalSurfacePairChart e (S ∩ E) (k '' D2) y false) := by
    intro y hy hyk
    simpa only [hps] using hkic y ⟨hps.symm.subset ⟨hy.1,interior_subset hy.2⟩,hy.2⟩ hyk
  rw [hcontact f hfR,hcontact k hkR]
  exact hmin k ⟨hk,hki,hkR,hkproper,hkno,hkb,hki'⟩

end PoincareConjecture.M76
