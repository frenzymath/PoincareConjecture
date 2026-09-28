import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalCircleFreeEssentialDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.NonboundingSphereContacts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalMarkedBigonProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OutermostSurfaceCompression
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialAnnulusBarrier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningFreeArcConfinement











set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_original_outermost_bigon_cases
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hI : IsPLIrreducible e (closure (latticeHandleDomain ι κ L \ D)))
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hn : ¬ ∃ B,B ⊆ latticeHandleDomain ι κ L ∧ Nonempty (ChartwisePLBall e B S))
    (pAnn : P2 → LatticeHandleAmbient ι κ L)
    (hpAnn : PolyhedralPLInCharts e pAnn Ann) (hpAi : InjOn pAnn Ann)
    {m : ℕ} (n : Fin m → ℕ) (P : ∀ i,Polygon P2 (n i+3))
    (hfamily : pAnn '' (⋃ i,(P i).boundary ℝ) = S ∩ frontier D)
    (hP : ∀ i,Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hdis : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    (hdepth : ∀ i z,z ∈ (P i).boundary ℝ → -1 < depth 8 z ∧ depth 8 z < 1)
    (hfront : pAnn '' Ann ⊆ frontier D)
    (hfull : frontier D ∩ interior (latticeHandleDomain ι κ L) ⊆ pAnn '' Ann)
    (hint : pAnn '' {z | -1 < depth 8 z ∧ depth 8 z < 1} ⊆
      interior (latticeHandleDomain ι κ L))
    (hends : ∀ z : Ann,pAnn z ∈ frontier (latticeHandleDomain ι κ L) ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1)
    (hencl : ∀ i,Dehn.annulusSquare 8 1 ⊆ (P i).inside)
    {K J q : Set P2} {p f : P2 → LatticeHandleAmbient ι κ L}
    (M : SurfaceIntersectionComponents K J p f q)
    (hJ : IsFinitePLBallPair P2 J q)
    (harcs : ∀ i,IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i ∩ q))
    (hf : PolyhedralPLInCharts e f J) (hfi : InjOn f J)
    (hfE : MapsTo f J (closure (latticeHandleDomain ι κ L \ D)))
    (hfproper : ∀ x ∈ J,f x ∈ frontier (closure (latticeHandleDomain ι κ L \ D)) ↔ x ∈ q)
    (hfno : ¬∃ F : C(J,frontier (closure (latticeHandleDomain ι κ L \ D))),
      ∀ x : J,(x : P2) ∈ q → (F x : LatticeHandleAmbient ι κ L) = f x)
    (hpimage : p '' K = S ∩ closure (latticeHandleDomain ι κ L \ D)) :
    ∃ k,∃ A U : Set P2,∃ a b : P2,
      a ≠ b ∧ IsFinitePLBallPair P2 A (U ∪ M.pieces k) ∧
      IsFinitePLBallPair ℝ U {a,b} ∧ IsFinitePLBallPair ℝ (M.pieces k) {a,b} ∧
      A ⊆ J ∧ PolyhedralPLInCharts e f A ∧ InjOn f A ∧
      f '' A ⊆ closure (latticeHandleDomain ι κ L \ D) ∧
      A ∩ q = U ∧ U ∩ M.pieces k = {a,b} ∧
      f '' A ∩ S = f '' M.pieces k ∧
      f '' A ∩ frontier (closure (latticeHandleDomain ι κ L \ D)) = f '' U ∧
      f '' (A \ (U ∪ M.pieces k)) ⊆ interior (closure (latticeHandleDomain ι κ L \ D)) \ S ∧
      ∃ i j : Fin m,∃ c d : P2,
        c ∈ (P i).boundary ℝ ∧ d ∈ (P j).boundary ℝ ∧ c ≠ d ∧
        f a = pAnn c ∧ f b = pAnn d ∧
        ((i = j ∧ f '' U ∩ pAnn '' (P i).boundary ℝ = {f a,f b}) ∨
          (i ≠ j ∧ f '' U ⊆ interior (latticeHandleDomain ι κ L) ∧
            f '' U ⊆ closure (latticeHandleDomain ι κ L \ D) ∩ D)) := by
  classical
  let X := LatticeHandleAmbient ι κ L
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  have hcontact : (S ∩ frontier D).Nonempty := by
    by_contra h
    exact hn (s.exists_ball_of_disjoint_ball_frontier he (isCompact_latticeHandleDomain ι κ L)
      b.ball b.subset_domain hI (hSR.trans interior_subset)
      (disjoint_left.mpr (fun x hxS hxD => h ⟨x,hxS,hxD⟩)))
  obtain ⟨x,hxS,hxD⟩ := hcontact
  obtain ⟨z,hz,_⟩ := hfamily.symm.subset ⟨hxS,hxD⟩
  obtain ⟨i₀,hzi⟩ := mem_iUnion.mp hz
  have hPS (i : Fin m) : pAnn '' (P i).boundary ℝ ⊆ S := by
    intro x hx
    exact (hfamily.subset ((image_mono (subset_iUnion _ i)) hx)).1
  have hDisk : IsFinitePLBallPair P2 Disk Rim :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨H,_,hHrim⟩ := hDisk.exists_homeomorph hJ
  let j : C(Disk,E) := ⟨fun z => ⟨f (H z),hfE (H z).property⟩,
    (hf.continuousOn.domRestrict.comp H.continuous).subtype_mk _⟩
  have hjfront (z : Rim) : (j ⟨z,sphere_subset_closedBall z.property⟩ : X) ∈ frontier E := by
    apply (hfproper _ (H _).property).mpr
    exact (hHrim ⟨z,sphere_subset_closedBall z.property⟩).mp z.property
  have hjno : ¬∃ F : C(Disk,frontier E),∀ z : Rim,
      (F ⟨z,sphere_subset_closedBall z.property⟩ : X) = j ⟨z,sphere_subset_closedBall z.property⟩ := by
    rintro ⟨F,hF⟩
    apply hfno
    refine ⟨F.comp ⟨H.symm,H.symm.continuous⟩,?_⟩
    intro z hz
    have hzr : (H.symm z : V2) ∈ Rim := (hHrim (H.symm z)).mpr (by rwa [H.apply_symm_apply])
    have hh := hF ⟨H.symm z,hzr⟩
    change (F (H.symm z) : X) = f (H (H.symm z)) at hh
    change (F (H.symm z) : X) = f z
    simpa only [H.apply_symm_apply] using hh
  obtain ⟨x,⟨z,rfl⟩,hxP⟩ := b.essential_disk_meets_enclosing_annular_circle
    he hdim hi pAnn hpAnn.continuousOn hpAi hfront hfull hint hends
      (P i₀) (hP i₀).2 (hP i₀).1 (hdepth i₀) (hencl i₀) j hjfront hjno
  have hmeet : (f '' J ∩ S).Nonempty :=
    ⟨j ⟨z,sphere_subset_closedBall z.property⟩,
      ⟨H ⟨z,sphere_subset_closedBall z.property⟩,(H _).property,rfl⟩,hPS i₀ hxP⟩
  obtain ⟨k,A,U,a,b₀,hab,hA,hU,hC,hAJ,hfA,hfiA,hAE,hAq,hUC,hAS,hAF,hAI⟩ :=
    exists_original_outermost_boundary_compression_disk M hJ harcs hf hfi hfE hfproper hpimage hmeet
  have haU : a ∈ U := hU.1 (by simp)
  have hbU : b₀ ∈ U := hU.1 (by simp)
  have haC : a ∈ M.pieces k := hC.1 (by simp)
  have hbC : b₀ ∈ M.pieces k := hC.1 (by simp)
  have hUA : U ⊆ A := subset_union_left.trans hA.1
  have hCA : M.pieces k ⊆ A := subset_union_right.trans hA.1
  have hendpoint (u : P2) (huU : u ∈ U) (huC : u ∈ M.pieces k) :
      ∃ i : Fin m,∃ c ∈ (P i).boundary ℝ,f u = pAnn c := by
    have huS : f u ∈ S := (hAS.symm.subset ⟨u,huC,rfl⟩).2
    have huF : f u ∈ frontier E := (hAF.symm.subset ⟨u,huU,rfl⟩).2
    have huD : f u ∈ frontier D :=
      (b.frontier_exterior_iff_interior he hdim hi (hSR huS)).mp huF
    obtain ⟨c,hc,hcu⟩ := hfamily.symm.subset ⟨huS,huD⟩
    obtain ⟨i,hci⟩ := mem_iUnion.mp hc
    exact ⟨i,c,hci,hcu.symm⟩
  obtain ⟨i,c,hc,hac⟩ := hendpoint a haU haC
  obtain ⟨j,d,hd,hbd⟩ := hendpoint b₀ hbU hbC
  have hcd : c ≠ d := by
    intro h
    exact hab (hfiA (hUA haU) (hUA hbU) (hac.trans ((congrArg pAnn h).trans hbd.symm)))
  refine ⟨k,A,U,a,b₀,hab,hA,hU,hC,hAJ,hfA,hfiA,hAE,hAq,hUC,hAS,hAF,hAI,
    i,j,c,d,hc,hd,hcd,hac,hbd,?_⟩
  by_cases hij : i = j
  · left
    refine ⟨hij,?_⟩
    apply Subset.antisymm
    · rintro x ⟨⟨u,hu,rfl⟩,hup⟩
      obtain ⟨v,hv,hvu⟩ := hAS.subset ⟨⟨u,hUA hu,rfl⟩,hPS i hup⟩
      have hvu' := hfiA (hCA hv) (hUA hu) hvu
      have huend := hUC.subset ⟨hu,hvu' ▸ hv⟩
      rcases huend with ha | hb
      · exact Or.inl (congrArg f ha)
      · exact Or.inr (congrArg f hb)
    · intro x hx
      rcases hx with ha | hb
      · rw [ha]
        exact ⟨⟨a,haU,rfl⟩,c,hc,hac.symm⟩
      · rw [hb]
        exact ⟨⟨b₀,hbU,rfl⟩,d,hij.symm ▸ hd,hbd.symm⟩
  · right
    refine ⟨hij,?_⟩
    exact b.original_spanning_free_arc_subset_lateral he hdim hi
      pAnn hpAnn.continuousOn hpAi hfront hfull hint hends
      (P i) (P j) (hP i).2 (hP i).1 (hP j).2 (hP j).1
      (hdepth i) (hdepth j) (hencl i) (hencl j) (hdis hij)
      (union_subset (hPS i) (hPS j)) hA (hUC.symm ▸ hU) hfA.continuousOn hfiA hAS hAF
      ⟨f a,⟨a,haU,rfl⟩,c,hc,hac.symm⟩
      ⟨f b₀,⟨b₀,hbU,rfl⟩,d,hd,hbd.symm⟩

theorem HamiltonMarkedProtectedBall.exists_circle_free_minimal_essential_disk_with_bigon_cases
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hI : IsPLIrreducible e (closure (latticeHandleDomain ι κ L \ D))) :
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
    (_hpp : ∀ z∈K.space,p z∈frontier E ↔ z∈B)
    (pAnn : P2 → LatticeHandleAmbient ι κ L)
    (_hpAnn : PolyhedralPLInCharts e pAnn Ann) (_hpAi : InjOn pAnn Ann)
    {m : ℕ} (n : Fin m → ℕ) (P : ∀ i,Polygon P2 (n i+3))
    (_hfamily : pAnn '' (⋃ i,(P i).boundary ℝ) = S ∩ frontier D)
    (_hP : ∀ i,Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (_hdis : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    (_hdepth : ∀ i z,z ∈ (P i).boundary ℝ → -1 < depth 8 z ∧ depth 8 z < 1)
    (_hfront : pAnn '' Ann ⊆ frontier D)
    (_hfull : frontier D ∩ interior (latticeHandleDomain ι κ L) ⊆ pAnn '' Ann)
    (_hint : pAnn '' {z | -1 < depth 8 z ∧ depth 8 z < 1} ⊆
      interior (latticeHandleDomain ι κ L))
    (_hends : ∀ z : Ann,pAnn z ∈ frontier (latticeHandleDomain ι κ L) ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1)
    (_hencl : ∀ i,Dehn.annulusSquare 8 1 ⊆ (P i).inside),
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
          (¬∃ i,∃ A U : Set P2,
            IsFinitePLBallPair P2 A (U ∪ C.pieces i) ∧
            IsFinitePLBallPair ℝ U (U ∩ C.pieces i) ∧
            A ⊆ K.space ∧ A ∩ B = U) ∧
    ∃ k,∃ A U : Set P2,∃ u0 u1 : P2,
      u0 ≠ u1 ∧ IsFinitePLBallPair P2 A (U ∪ M.pieces k) ∧
      IsFinitePLBallPair ℝ U {u0,u1} ∧ IsFinitePLBallPair ℝ (M.pieces k) {u0,u1} ∧
      A ⊆ J.space ∧ PolyhedralPLInCharts e (f ∘ a.symm) A ∧ InjOn (f ∘ a.symm) A ∧
      (f ∘ a.symm) '' A ⊆ closure (latticeHandleDomain ι κ L \ D) ∧
      A ∩ frontier J.space = U ∧ U ∩ M.pieces k = {u0,u1} ∧
      (f ∘ a.symm) '' A ∩ S = (f ∘ a.symm) '' M.pieces k ∧
      (f ∘ a.symm) '' A ∩ frontier (closure (latticeHandleDomain ι κ L \ D)) = (f ∘ a.symm) '' U ∧
      (f ∘ a.symm) '' (A \ (U ∪ M.pieces k)) ⊆ interior (closure (latticeHandleDomain ι κ L \ D)) \ S ∧
      ∃ i j : Fin m,∃ c d : P2,
        c ∈ (P i).boundary ℝ ∧ d ∈ (P j).boundary ℝ ∧ c ≠ d ∧
        (f ∘ a.symm) u0 = pAnn c ∧ (f ∘ a.symm) u1 = pAnn d ∧
        ((i = j ∧ (f ∘ a.symm) '' U ∩ pAnn '' (P i).boundary ℝ = {(f ∘ a.symm) u0,(f ∘ a.symm) u1}) ∨
          (i ≠ j ∧ (f ∘ a.symm) '' U ⊆ interior (latticeHandleDomain ι κ L) ∧
            (f ∘ a.symm) '' U ⊆ closure (latticeHandleDomain ι κ L \ D) ∩ D)) ∧
      ∀ O : Set X, IsOpen O → (f ∘ a.symm) '' A ⊆ O →
    ∃ (W : Set X) (H : Disk ≃ₜ A) (j : V2 → X)
      (T : OriginalDiskProduct e (E ∩ W) j),
      PLDomain e W ∧ frontier W = S ∧
      IsCompact (E ∩ W) ∧ PLDomain e (E ∩ W) ∧
      frontier (E ∩ W) = (E ∩ W) ∩ (frontier E ∪ S) ∧
      IsCompact (D ∩ W) ∧ PLDomain e (D ∩ W) ∧
      frontier (D ∩ W) = (D ∩ W) ∩ (frontier D ∪ S) ∧
      H.IsFinitePL ∧ (∀ z : Disk, j z = (f ∘ a.symm) (H z)) ∧
      (∀ z : Disk, (z : V2) ∈ Rim ↔ (H z : P2) ∈ U ∪ M.pieces k) ∧
      MapsTo T.map (Disk ×ˢ I) O ∧
      T.map '' (Disk ×ˢ {(0 : ℝ)}) = (f ∘ a.symm) '' A ∧
      (∀ z : Disk, j z ∈ frontier E ↔ (H z : P2) ∈ U) ∧
      (∀ z : Disk, j z ∈ S ↔ (H z : P2) ∈ M.pieces k) ∧
      (∀ z ∈ Rim, ∀ t ∈ I,
        (T.map (z,t) ∈ frontier E ↔ j z ∈ frontier E) ∧
        (T.map (z,t) ∈ S ↔ j z ∈ S)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : ↥(E ∩ W) → X) ⁻¹' (T.map '' (Disk ×ˢ Ioo (-v) v))) := by
  classical
  intro X R E s hSR hn Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin
    K hK B p hp hpi hps hpp pAnn hpAnn hpAi m n P hfamily hP hdis hdepth
    hfront hfull hint hends hencl disks a
  obtain ⟨f,hf,hfmin,hfmodel,J,hJ,hJs,hJball,hfPL,hfi,hfE,hfproper,hfbc,hfic,
    hfno,C,M,harcs,hreturn⟩ :=
    b.exists_circle_free_minimal_essential_disk he hdim hi s hSR hn Q G
      hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin K hK p hp hpi hps hpp
  have hcases := b.exists_original_outermost_bigon_cases he hdim hi hI s hSR hn
    pAnn hpAnn hpAi n P hfamily hP hdis hdepth hfront hfull hint hends hencl
    M hJball harcs hfPL hfi hfE hfproper hfno hps
  obtain ⟨k,A,U,u0,u1,hu,hA,hU,hC,hAJ,hfA,hfiA,hAE,hAq,hUC,hAS,hAF,hAI,
    i,j,c,d,hc,hd,hcd,h0,h1,hcase⟩ := hcases
  have hcrossO : ∀ x ∈ S ∩ frontier E,∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0 := by
    intro x hx
    obtain ⟨T,hxT,_,_,hT0,hT,_,hTS,hTE⟩ :=
      hcross (Q x) (hGs.symm.subset (mem_image_of_mem Q hx)) univ isOpen_univ (mem_univ _)
    exact compatible_paired_chart_of_coordinate_crossing Q hQ T hT (hCQ hx) hxT hT0 hTS hTE
  have hbdy : ∀ x ∈ S ∩ frontier E,x ∈ (f ∘ a.symm) '' J.space →
      ∃ B : OriginalSurfacePairChart e ((f ∘ a.symm) '' J.space) (S ∩ E) x true,
        (∀ z ∈ B.coordinates.source,B.chart.symm z ∈ E ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source,B.chart.symm z ∈ frontier E ↔ (B.coordinates z).1.2 = 0 := by
    intro x hx hxf
    obtain ⟨B,hBE,hBF⟩ := hfbc x hx hxf
    exact B.swap_boundary_region hBE hBF
  refine ⟨f,hf,hfmin,hfmodel,J,hJ,hJs,hJball,hfPL,hfi,hfE,hfproper,hfbc,hfic,
    hfno,C,M,harcs,hreturn,k,A,U,u0,u1,hu,hA,hU,hC,hAJ,hfA,hfiA,hAE,hAq,hUC,hAS,hAF,hAI,
    i,j,c,d,hc,hd,hcd,h0,h1,hcase,?_⟩
  intro O hO hAO
  exact b.exists_original_marked_bigon_product he hdim hi s hSR hcrossO
    hA hu hUC hfA hfiA (image_subset_iff.mp hAE) hAF hAS
    (image_mono hAJ) hbdy hO hAO

end PoincareConjecture.M76
