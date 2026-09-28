import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalOutermostBigonCases
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcSameSide
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalRelativeCompressionContradiction









set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip
namespace PoincareConjecture.M76
open Dehn.Annuli.BoundaryUnionDisk
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "C3" => ((ℝ × ℝ) × ℝ)
noncomputable local instance : DecidableEq P2 := fun _ _ => Classical.propDecidable _
theorem HamiltonMarkedProtectedBall.no_equal_endpoint_outermost_bigon_at_minimum
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
    (_hencl : ∀ i,Dehn.annulusSquare 8 1 ⊆ (P i).inside)
    (J : SimplicialComplex ℝ P2) {f : P2 → X}
    (C : SurfaceIntersectionComponents J.space K.space f p B)
    (M : SurfaceIntersectionComponents K.space J.space p f (frontier J.space))
    (_hfi : InjOn f J.space)
    (_hfproper : ∀ z∈J.space,f z∈frontier E ↔ z∈frontier J.space)
    (_harcs : ∀ i,IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i∩frontier J.space))
    (_hno : ¬∃ i,∃ A U : Set P2,
      IsFinitePLBallPair P2 A (U ∪ C.pieces i) ∧
      IsFinitePLBallPair ℝ U (U ∩ C.pieces i) ∧ A ⊆ K.space ∧ A ∩ B = U)
    (_hfbc : ∀ y∈S∩frontier E,y∈f '' J.space →
      ∃ T : OriginalSurfacePairChart e (S∩E) (f '' J.space) y true,
        (∀ v∈T.coordinates.source,T.chart.symm v∈E ↔ 0≤(T.coordinates v).1.2) ∧
        ∀ v∈T.coordinates.source,T.chart.symm v∈frontier E ↔ (T.coordinates v).1.2=0)
    (k : M.right.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {A U : Set P2} {u0 u1 : P2}
    (_hu : u0 ≠ u1) (_hA : IsFinitePLBallPair P2 A (U ∪ M.pieces k))
    (_hU : IsFinitePLBallPair ℝ U {u0,u1})
    (_hC : IsFinitePLBallPair ℝ (M.pieces k) {u0,u1})
    (_hAJ : A ⊆ J.space) (_hfA : PolyhedralPLInCharts e f A)
    (_hAE : f '' A ⊆ E) (_hAq : A ∩ frontier J.space = U)
    (_hUC : U ∩ M.pieces k = {u0,u1})
    (_hAS : f '' A ∩ S = f '' M.pieces k)
    (_hAF : f '' A ∩ frontier E = f '' U)
    (i : Fin m) {c d : P2}
    (_hc : c∈(P i).boundary ℝ) (_hd : d∈(P i).boundary ℝ) (_hcd : c≠d)
    (_h0 : f u0=pAnn c) (_h1 : f u1=pAnn d)
    (_hinter : f '' U ∩ pAnn '' (P i).boundary ℝ={f u0,f u1}), False := by
  classical
  intro X R E s hSR hn Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin
    K hK B p hp hpi hps hpp pAnn hpAnn hpAi m n P hfamily hP hdis hdepth
    hfront hfull hint hends hencl J f C M hfi hfproper harcs hno hfbc k
    A U u0 u1 hu hA hU hC hAJ hfA hAE hAq hUC hAS hAF i c d hc hd hcd h0 h1 hinter
  have hcrossO : ∀ x ∈ S ∩ frontier E,∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ T x = 0 ∧
      (∀ a,(e a).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ T.source,y ∈ S ↔ T y 1 = 0) ∧
      ∀ y ∈ T.source,y ∈ frontier E ↔ T y 0 = 0 := by
    intro x hx
    obtain ⟨T,hxT,_,_,hT0,hT,_,hTS,hTE⟩ :=
      hcross (Q x) (hGs.symm.subset (mem_image_of_mem Q hx)) univ isOpen_univ (mem_univ _)
    exact compatible_paired_chart_of_coordinate_crossing Q hQ T hT (hCQ hx) hxT hT0 hTS hTE
  have hbdy : ∀ x ∈ S ∩ frontier E,x ∈ f '' J.space →
      ∃ T : OriginalSurfacePairChart e (f '' J.space) (S ∩ E) x true,
        (∀ z ∈ T.coordinates.source,T.chart.symm z ∈ E ↔ 0 ≤ (T.coordinates z).1.2) ∧
        ∀ z ∈ T.coordinates.source,T.chart.symm z ∈ frontier E ↔ (T.coordinates z).1.2 = 0 := by
    intro x hx hxf
    obtain ⟨T,hTE,hTF⟩ := hfbc x hx hxf
    exact T.swap_boundary_region hTE hTF
  have hfiA := hfi.mono hAJ
  obtain ⟨W,H,j0,T,heW,hWS,_,heEW,_,_,_,_,_,_,_,_,hcenter,_⟩ :=
    b.exists_original_marked_bigon_product he hdim hi s hSR hcrossO
      hA hu hUC hfA hfiA (image_subset_iff.mp hAE) hAF hAS (image_mono hAJ)
      hbdy isOpen_univ (subset_univ _)
  have hPS : pAnn '' (P i).boundary ℝ ⊆ S := fun x hx =>
    (hfamily.subset (image_mono (subset_iUnion _ i) hx)).1
  obtain ⟨V0,V1,hV0,hV1,hVs,hVint,Z,hZchoice,j,hj,hji,hjF,hjr,hjS,hAj,
      g,hg,hgi,hgimage,hgrim,hgE,hgS,hgF,hjW,hjiW,hgEW⟩ :=
    b.exists_original_terminal_disk_union_in_marked_side he hdim hi pAnn hpAnn hpAi
      hfront hfull hint hends (P i) (hP i).2 (hP i).1 (hdepth i) (hencl i)
      s hA hU hC hUC hu hfA hfiA hAS hAF hPS hc hd hcd h0 h1 hinter
      hSR m n P i rfl hfamily hP hdis hdepth hencl heW.closed hWS T hcenter
  have hZ : IsFinitePLBallPair ℝ Z {c,d} :=
    hZchoice.elim (fun h => h.symm ▸ hV0) (fun h => h.symm ▸ hV1)
  have hZP : Z ⊆ (P i).boundary ℝ := by
    rcases hZchoice with rfl | rfl
    · exact subset_union_left.trans hVs.subset
    · exact subset_union_right.trans hVs.subset
  have hZAnn : Z ⊆ Ann := fun z hz => mem_squareAnnulus_iff_depth.mpr
    ⟨(hdepth i z (hZP hz)).1.le,(hdepth i z (hZP hz)).2.le⟩
  have hpZ : PolyhedralPLInCharts e pAnn Z := by
    have hZcopy := hZ
    obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := hZcopy
    exact hLs ▸ hpAnn.restrict_finite L hL (hLs.subset.trans hZAnn)
  obtain ⟨equiv,hequiv⟩ := C.exists_component_equiv M
  let l := equiv k
  have hmatch : f '' M.pieces k = p '' C.pieces l := hequiv k
  have hCK : C.pieces l ⊆ K.space := fun x hx =>
    (C.right_space.subset (C.cover.symm.subset (mem_iUnion.mpr ⟨l,hx⟩))).1
  have hrims : ∀ x∈J.space,∀ y∈K.space,f x=p y →
      (x∈frontier J.space ↔ y∈B) := by
    intro x hx y hy hxy
    rw [←hfproper x hx,←hpp y hy,hxy]
  have hCl := C.interval_models_of_paired_intervals M hfi hpi hrims harcs l
  have hCA : M.pieces k ⊆ A := subset_union_right.trans hA.1
  have hMends : M.pieces k ∩ frontier J.space = {u0,u1} := by
    apply Subset.antisymm
    · intro x hx
      exact hUC.subset ⟨hAq.subset ⟨hCA hx.1,hx.2⟩,hx.1⟩
    · intro x hx
      have hx' := hUC.symm.subset hx
      exact ⟨hx'.2,(hAq.symm.subset hx'.1).2⟩
  have hpend : p '' (C.pieces l ∩ B) = f '' {u0,u1} := by
    rw [←hMends]
    apply Subset.antisymm
    · rintro _ ⟨y,hy,rfl⟩
      obtain ⟨x,hx,hxy⟩ := hmatch.symm.subset ⟨y,hy.1,rfl⟩
      exact ⟨x,⟨hx,(hrims x (hAJ (hCA hx)) y (hCK hy.1) hxy).mpr hy.2⟩,hxy⟩
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hyx⟩ := hmatch.subset ⟨x,hx.1,rfl⟩
      exact ⟨y,⟨hy,(hrims x (hAJ (hCA hx.1)) y (hCK hy) hyx.symm).mp hx.2⟩,hyx⟩
  have hZends : pAnn '' {c,d} = p '' (C.pieces l ∩ B) := by
    rw [hpend]
    simp only [image_insert_eq,image_singleton,h0,h1]
  have hpZF : pAnn '' Z ⊆ S ∩ frontier E := by
    intro x hx
    have hxs := hPS (image_mono hZP hx)
    have hxd := hfront (image_mono hZAnn hx)
    exact ⟨hxs,(b.frontier_exterior_iff_interior he hdim hi (hSR hxs)).mpr hxd⟩
  have hinterZ : p '' C.pieces l ∩ pAnn '' Z = p '' (C.pieces l ∩ B) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x,hx,rfl⟩,hxZ⟩
      exact ⟨x,⟨hx,(hpp x (hCK hx)).mp (hpZF hxZ).2⟩,rfl⟩
    · intro x hx
      exact ⟨image_mono inter_subset_left hx,image_mono hZ.1 (hZends.symm.subset hx)⟩
  have hnoL : ¬∃ D0 U0 : Set P2,IsFinitePLBallPair P2 D0 (U0∪C.pieces l) ∧
      IsFinitePLBallPair ℝ U0 (U0∩C.pieces l) ∧ D0⊆K.space ∧ D0∩B=U0 := by
    rintro ⟨D0,U0,hD0,hU0,hD0K,hD0B⟩
    exact hno ⟨l,D0,U0,hD0,hU0,hD0K,hD0B⟩
  have hgeom := b.closed_complement_geometry he hdim hi
  exact s.no_returning_disk_in_original_sphere_side_at_minimum he
    (b.plDomain_closed_complement he hdim hi) (isCompact_latticeHandleDomain ι κ L)
    hSR hn isClosed_closure hgeom.2.1 Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin
    K hK p hp hpi hps hpp hCl hCK pAnn hpZ (hpAi.mono hZAnn) hZ hpZF
    hZends hinterZ hnoL hgeom.1 heW heEW hWS whole_ball g hg hgi hgEW hgS
    (hgrim.trans (congrArg (fun A0 => A0 ∪ pAnn '' Z) hmatch))


end PoincareConjecture.M76

