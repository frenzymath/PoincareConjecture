import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialDiskCircleFree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialDiskCircleMinimum
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningArcExclusion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningDiskMinimum












set_option autoImplicit false
open Set Metric Geometry Topology
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

open Classical in
theorem HamiltonMarkedProtectedBall.exists_circle_free_minimal_essential_disk
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀
    (_s : ChartwisePLSphere e S)
    (_hSR : S ⊆ interior R)
    (_hn : ¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S))
    (Q : OpenPartialHomeomorph X V3) (G : SimplicialComplex ℝ V3)
    (_hDQ : D ⊆ Q.source)
    (_hQ : ∀ a, (e a).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (_hCQ : S ∩ frontier E ⊆ Q.source)
    (_hG : G.faces.Finite) (_hGs : G.space = Q '' (S ∩ frontier E))
    (_hpres : HasDisjointPolygonPresentation G.space)
    (_hGc : ∀ a ∈ G.faces, a.card ≤ 2)
    (_hdegree : ∀ v : G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (_hcross : ∀ w ∈ G.space, ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ C : OpenPartialHomeomorph V3 C3,
        w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
        (∀ z ∈ C.source, Q.symm z ∈ interior R) ∧ C w = 0 ∧
        LocallyPiecewiseAffineOn C C.source ∧
        LocallyPiecewiseAffineOn C.symm C.target ∧
        (∀ x ∈ C.source, Q.symm x ∈ S ↔ (C x).2 = 0) ∧
        ∀ x ∈ C.source, Q.symm x ∈ frontier E ↔ (C x).1.1 = 0)
    (_hmin : ∀ d : Set X × OpenPartialHomeomorph X V3 × SimplicialComplex ℝ V3,
      (Nonempty (ChartwisePLSphere e d.1) ∧ d.1 ⊆ interior R ∧
        (¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B d.1)) ∧
        D ⊆ d.2.1.source ∧
        (∀ a, (e a).symm.trans d.2.1 ∈ piecewiseAffineGroupoid V3) ∧
        d.1 ∩ frontier E ⊆ d.2.1.source ∧
        d.2.2.faces.Finite ∧ d.2.2.space = d.2.1 '' (d.1 ∩ frontier E) ∧
        HasDisjointPolygonPresentation d.2.2.space ∧
        (∀ a ∈ d.2.2.faces, a.card ≤ 2) ∧
        (∀ v : d.2.2.vertices,
          (d.2.2.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
        ∀ w ∈ d.2.2.space, ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ C : OpenPartialHomeomorph V3 C3,
            w ∈ C.source ∧ C.source ⊆ O ∩ d.2.1.target ∧
            (∀ z ∈ C.source, d.2.1.symm z ∈ interior R) ∧ C w = 0 ∧
            LocallyPiecewiseAffineOn C C.source ∧
            LocallyPiecewiseAffineOn C.symm C.target ∧
            (∀ x ∈ C.source, d.2.1.symm x ∈ d.1 ↔ (C x).2 = 0) ∧
            ∀ x ∈ C.source, d.2.1.symm x ∈ frontier E ↔ (C x).1.1 = 0) →
      Nat.card (ConnectedComponents G.space) ≤
        Nat.card (ConnectedComponents d.2.2.space))
    (K : SimplicialComplex ℝ P2) (_hK : K.faces.Finite) {B : Set P2}
    (p : P2 → X) (_hp : PolyhedralPLInCharts e p K.space) (_hpi : InjOn p K.space)
    (_hps : p '' K.space=S∩E)
    (_hpp : ∀ z∈K.space,p z∈frontier E ↔ z∈B),
    let disks : Set (V2 → X) := {j |
      PolyhedralPLInCharts e j D2 ∧ IsEmbedding (fun x : D2 => j x) ∧
      MapsTo j D2 E ∧ (∀ x : D2,j x∈frontier E ↔ (x : V2)∈Q2) ∧
      (¬ ∃ F : C(D2,frontier E),∀ x : Q2,
        (F ⟨x,sphere_subset_closedBall x.property⟩ : X)=j x) ∧
      (∀ y∈S∩frontier E,y∈j '' D2 →
        ∃ C : OriginalSurfacePairChart e (S∩E) (j '' D2) y true,
          (∀ v∈C.coordinates.source,C.chart.symm v∈E ↔ 0≤(C.coordinates v).1.2) ∧
          ∀ v∈C.coordinates.source,C.chart.symm v∈frontier E ↔ (C.coordinates v).1.2=0) ∧
      ∀ y∈S∩interior E,y∈j '' D2 →
        Nonempty (OriginalSurfacePairChart e (S∩E) (j '' D2) y false)}
    let a := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
    ∃ f∈disks,
      (∀ k∈disks,Nat.card (ConnectedComponents (D2∩f ⁻¹' S : Set V2))≤
        Nat.card (ConnectedComponents (D2∩k ⁻¹' S : Set V2))) ∧
      Nonempty (SurfaceIntersectionComponents K.space D2 p f Q2) ∧
      ∃ (J : SimplicialComplex ℝ P2),J.faces.Finite ∧ J.space=a '' D2 ∧
        IsFinitePLBallPair P2 J.space (frontier J.space) ∧
        PolyhedralPLInCharts e (f∘a.symm) J.space ∧ InjOn (f∘a.symm) J.space ∧
        MapsTo (f∘a.symm) J.space E ∧
        (∀ z∈J.space,(f∘a.symm) z∈frontier E ↔ z∈frontier J.space) ∧
        (∀ y∈S∩frontier E,y∈(f∘a.symm) '' J.space →
          ∃ C : OriginalSurfacePairChart e (S∩E) ((f∘a.symm) '' J.space) y true,
            (∀ v∈C.coordinates.source,C.chart.symm v∈E ↔ 0≤(C.coordinates v).1.2) ∧
            ∀ v∈C.coordinates.source,C.chart.symm v∈frontier E ↔ (C.coordinates v).1.2=0) ∧
        (∀ y∈S∩interior E,y∈(f∘a.symm) '' J.space →
          Nonempty (OriginalSurfacePairChart e (S∩E) ((f∘a.symm) '' J.space) y false)) ∧
        (¬ ∃ F : C(J.space,frontier E),∀ x : J.space,(x : P2)∈frontier J.space →
          (F x : X)=(f∘a.symm) x) ∧
        ∃ (C : SurfaceIntersectionComponents J.space K.space (f∘a.symm) p B)
          (M : SurfaceIntersectionComponents K.space J.space p (f∘a.symm) (frontier J.space)),
          (∀ i,IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i∩frontier J.space)) ∧
          ¬∃ i,∃ A U : Set P2,
            IsFinitePLBallPair P2 A (U ∪ C.pieces i) ∧
            IsFinitePLBallPair ℝ U (U ∩ C.pieces i) ∧
            A ⊆ K.space ∧ A ∩ B = U := by
  classical
  intro X R E s hSR hn Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin
    K hK B p hp hpi hps hpp disks a
  have heE := b.plDomain_closed_complement he hdim hi
  have hgeom := b.closed_complement_geometry he hdim hi
  have hcrossO : ∀ x∈S∩frontier E,∃ H : OpenPartialHomeomorph X V3,
      x∈H.source ∧ H x=0 ∧
      (∀ i,(e i).symm.trans H∈piecewiseAffineGroupoid V3) ∧
      (∀ y∈H.source,y∈S ↔ H y 1=0) ∧
      ∀ y∈H.source,y∈frontier E ↔ H y 0=0 := by
    intro x hx
    obtain ⟨C,hxC,_,_,hC0,hC,_,hCS,hCE⟩ :=
      hcross (Q x) (hGs.symm.subset (mem_image_of_mem Q hx)) univ isOpen_univ (mem_univ _)
    exact compatible_paired_chart_of_coordinate_crossing Q hQ C hC (hCQ hx) hxC hC0 hCS hCE
  obtain ⟨f,hf,hfmin,hmodel,J,hJ,hJs,C,hnull,⟨M⟩⟩ :=
    b.exists_minimal_essential_disk_without_null_circle he hdim hi s K hK p hp hpi hps hpp hcrossO
  change J.space=a '' D2 at hJs
  have hfspec := hf
  obtain ⟨hfPL,hfi,hfE,hfproper,hfno,hfbc,hfic⟩ := hf
  have hJcv : Convex ℝ J.space := hJs.symm ▸
    (convex_closedBall (0 : V2) 1).linear_image a.toLinearMap
  have hJfront : frontier J.space=a '' Q2 := by
    rw [hJs]
    change frontier (a.toHomeomorph '' D2)=a.toHomeomorph '' Q2
    rw [←a.toHomeomorph.image_frontier,frontier_closedBall _ (by norm_num : (1:ℝ)≠0)]
  have hJball : IsFinitePLBallPair P2 J.space (frontier J.space) := by
    have hstd := (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
    have hh := hstd.affine_image a.toContinuousLinearMap.toContinuousAffineMap a.injective.injOn
    change IsFinitePLBallPair P2 (a '' D2) (a '' Q2) at hh
    rwa [←hJs,←hJfront] at hh
  have hback (x : P2) (hx : x∈J.space) : a.symm x∈D2 := by
    obtain ⟨y,hy,rfl⟩ := hJs.subset hx
    simpa using hy
  have hfront (x : P2) : x∈frontier J.space ↔ a.symm x∈Q2 := by
    rw [hJfront]
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
    · intro hx
      exact ⟨a.symm x,hx,a.apply_symm_apply x⟩
  let f0 : P2 → X := f∘a.symm
  have hf0 : PolyhedralPLInCharts e f0 J.space :=
    hfPL.comp_finitePiecewiseAffineOn J hJ
      ((J.affineOnFaces_affine a.symm.toContinuousLinearMap.toContinuousAffineMap).finitePiecewiseAffineOn hJ)
      hback
  have hf0i : InjOn f0 J.space := by
    intro x hx y hy hxy
    exact a.symm.injective (congrArg Subtype.val (hfi.injective
      (a₁ := ⟨a.symm x,hback x hx⟩) (a₂ := ⟨a.symm y,hback y hy⟩) hxy))
  have hf0E : MapsTo f0 J.space E := fun x hx => hfE (hback x hx)
  have hf0proper : ∀ z∈J.space,f0 z∈frontier E ↔ z∈frontier J.space :=
    fun z hz => (hfproper ⟨a.symm z,hback z hz⟩).trans (hfront z).symm
  have hf0image : f0 '' J.space=f '' D2 := by
    rw [hJs,Set.image_image]
    simp only [f0,Function.comp_apply,a.symm_apply_apply]
  have hf0bc : ∀ y∈S∩frontier E,y∈f0 '' J.space →
      ∃ C : OriginalSurfacePairChart e (S∩E) (f0 '' J.space) y true,
        (∀ v∈C.coordinates.source,C.chart.symm v∈E ↔ 0≤(C.coordinates v).1.2) ∧
        ∀ v∈C.coordinates.source,C.chart.symm v∈frontier E ↔ (C.coordinates v).1.2=0 := by
    intro y hy hyf
    rw [hf0image]
    exact hfbc y hy (hf0image.subset hyf)
  have hf0ic : ∀ y∈S∩interior E,y∈f0 '' J.space →
      Nonempty (OriginalSurfacePairChart e (S∩E) (f0 '' J.space) y false) := by
    intro y hy hyf
    rw [hf0image]
    exact hfic y hy (hf0image.subset hyf)
  have hf0no : ¬ ∃ F : C(J.space,frontier E),∀ x : J.space,(x : P2)∈frontier J.space →
      (F x : X)=f0 x := by
    rintro ⟨F,hF⟩
    let H : D2 ≃ₜ J.space := (a.toHomeomorph.image D2).trans (Homeomorph.setCongr hJs.symm)
    refine hfno ⟨F.comp ⟨H,H.continuous⟩,?_⟩
    intro x
    have hxfr : a x∈frontier J.space :=
      (hfront (a x)).mpr (by simpa only [a.symm_apply_apply] using x.property)
    have hh := hF ⟨a x,hJball.1 hxfr⟩ hxfr
    change (F ⟨a x,_⟩ : X)=f x
    simpa only [f0,Function.comp_apply,a.symm_apply_apply] using hh
  have harcs := s.contact_intervals_of_sphere_and_disk_minima he
    (isCompact_latticeHandleDomain ι κ L) hSR hn isClosed_closure hgeom.2.1
    Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin
    heE K hK p hp hpi hps hpp J hJcv f0 hf0 hf0i hf0E hf0proper C M hnull
  refine ⟨f,hfspec,hfmin,hmodel,J,hJ,hJs,hJball,hf0,hf0i,hf0E,hf0proper,hf0bc,hf0ic,
    hf0no,C,M,harcs,?_⟩
  have hf0no' : ¬∃ F : C(J.space,frontier E),∀ x : frontier J.space,
      (F ⟨x,hJball.1 x.property⟩ : X) = f0 x := by
    rintro ⟨F,hF⟩
    exact hf0no ⟨F,fun x hx => hF ⟨x,hx⟩⟩
  have hb0 : ∀ x ∈ J.space,f0 x ∈ p '' K.space → f0 x ∈ frontier E →
      ∃ C : OriginalSurfacePairChart e (f0 '' J.space) (p '' K.space) (f0 x) true,
        (∀ z ∈ C.coordinates.source,C.chart.symm z ∈ E ↔ 0 ≤ (C.coordinates z).1.2) ∧
        ∀ z ∈ C.coordinates.source,C.chart.symm z ∈ frontier E ↔ (C.coordinates z).1.2 = 0 := by
    intro x hx hxp hxf
    obtain ⟨T,hTE,hTF⟩ := hf0bc (f0 x) ⟨(hps.subset hxp).1,hxf⟩ (mem_image_of_mem f0 hx)
    rw [hps]
    exact T.swap_boundary_region hTE hTF
  have hi0 : ∀ x ∈ J.space,f0 x ∈ p '' K.space → f0 x ∈ interior E →
      Nonempty (OriginalSurfacePairChart e (f0 '' J.space) (p '' K.space) (f0 x) false) := by
    intro x hx hxp hxf
    obtain ⟨T⟩ := hf0ic (f0 x) ⟨(hps.subset hxp).1,hxf⟩ (mem_image_of_mem f0 hx)
    rw [hps]
    exact ⟨T.swap⟩
  apply s.no_returning_disk_at_essential_minimum hgeom.1 heE J K hJ hK hJball
    hf0 hp hf0i hpi hf0E (fun x hx => (hps.subset (mem_image_of_mem p hx)).2)
    hf0proper hpp hf0no' hb0 hi0 ?_ C M harcs hps hcrossO
  intro k hk hki hkE hkp hkno hkb hkin
  apply essential_disk_minimum_in_planar_coordinates f ?_ J hJs k hk hki hkE hkp ?_ hkb hkin
  · intro k0 hk0 hk0i hk0E hk0p hk0no hk0b hk0in
    have hcontact (j : V2 → X) (hj : MapsTo j D2 E) :
        D2 ∩ j ⁻¹' (p '' K.space) = D2 ∩ j ⁻¹' S := by
      ext x
      simp only [mem_inter_iff,mem_preimage,hps]
      exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hj h.1⟩⟩
    have hk0b' : ∀ y ∈ S ∩ frontier E,y ∈ k0 '' D2 →
        ∃ T : OriginalSurfacePairChart e (S ∩ E) (k0 '' D2) y true,
          (∀ z ∈ T.coordinates.source,T.chart.symm z ∈ E ↔ 0 ≤ (T.coordinates z).1.2) ∧
          ∀ z ∈ T.coordinates.source,T.chart.symm z ∈ frontier E ↔ (T.coordinates z).1.2 = 0 := by
      intro y hy hyk
      have hyE : y ∈ E := by
        obtain ⟨x,hx,rfl⟩ := hyk
        exact hk0E hx
      have hh := hk0b y ⟨hps.symm.subset ⟨hy.1,hyE⟩,hy.2⟩ hyk
      rwa [hps] at hh
    have hk0in' : ∀ y ∈ S ∩ interior E,y ∈ k0 '' D2 →
        Nonempty (OriginalSurfacePairChart e (S ∩ E) (k0 '' D2) y false) := by
      intro y hy hyk
      have hh := hk0in y ⟨hps.symm.subset ⟨hy.1,interior_subset hy.2⟩,hy.2⟩ hyk
      rwa [hps] at hh
    rw [hcontact f hfE,hcontact k0 hk0E]
    exact hfmin k0 ⟨hk0,hk0i,hk0E,hk0p,hk0no,hk0b',hk0in'⟩
  · rintro ⟨F,hF⟩
    exact hkno ⟨F,fun x => hF ⟨x,hJball.1 x.property⟩ x.property⟩

end PoincareConjecture.M76
