import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBigonExclusion

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "C3" => ((ℝ × ℝ) × ℝ)
noncomputable local instance : DecidableEq P2 := fun _ _ => Classical.propDecidable _
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_circle_free_minimal_essential_disk_with_spanning_bigon
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
        (i ≠ j ∧ (f ∘ a.symm) '' U ⊆ interior (latticeHandleDomain ι κ L) ∧
          (f ∘ a.symm) '' U ⊆ closure (latticeHandleDomain ι κ L \ D) ∩ D) ∧
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
      hfno,C,M,harcs,hreturn,k,A,U,u0,u1,hu,hA,hU,hC,hAJ,hfA,hfiA,hAE,
      hAq,hUC,hAS,hAF,hAI,i,j,c,d,hc,hd,hcd,h0,h1,hcase,hproduct⟩ :=
    b.exists_circle_free_minimal_essential_disk_with_bigon_cases he hdim hi hI
      s hSR hn Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin
      K hK p hp hpi hps hpp pAnn hpAnn hpAi n P hfamily hP hdis hdepth
      hfront hfull hint hends hencl
  have hspan : i ≠ j ∧ (f ∘ a.symm) '' U ⊆ interior R ∧
      (f ∘ a.symm) '' U ⊆ E ∩ D := by
    rcases hcase with ⟨hij,hinter⟩ | hspan
    · subst j
      exact False.elim (b.no_equal_endpoint_outermost_bigon_at_minimum he hdim hi
        s hSR hn Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin K hK p hp hpi hps hpp
        pAnn hpAnn hpAi n P hfamily hP hdis hdepth hfront hfull hint hends hencl
        J C M hfi hfproper harcs hreturn hfbc k hu hA hU hC hAJ hfA hAE hAq
        hUC hAS hAF i hc hd hcd h0 h1 hinter)
    · exact hspan
  exact ⟨f,hf,hfmin,hfmodel,J,hJ,hJs,hJball,hfPL,hfi,hfE,hfproper,hfbc,hfic,
    hfno,C,M,harcs,hreturn,k,A,U,u0,u1,hu,hA,hU,hC,hAJ,hfA,hfiA,hAE,
    hAq,hUC,hAS,hAF,hAI,i,j,c,d,hc,hd,hcd,h0,h1,hspan,hproduct⟩

end PoincareConjecture.M76
