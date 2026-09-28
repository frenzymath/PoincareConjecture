import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ClosedIrreducibleSphere
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorPosition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalConfinedSphereBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedArcSphereObstruction
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.RetainedBallTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreComponentCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ActualFaceComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.NonboundingExteriorSurface
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.NonboundingFrontierDiskStep
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ContactSubcomplex
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalAnnularContactAlternatives








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "P2" => (ℝ × ℝ)

theorem ChartwisePLSphere.exists_ball_of_disjoint_ball_frontier
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R D S : Set X}
    (he : PLDomain e R) (hR : IsCompact R)
    (b : ChartwisePLBall e D (frontier D)) (hDR : D ⊆ R)
    (hI : IsPLIrreducible e (closure (R \ D)))
    (s : ChartwisePLSphere e S) (hSR : S ⊆ R)
    (hdis : Disjoint S (frontier D)) :
    ∃ B : Set X, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S) := by
  rcases preconnected_interior_or_exterior_of_frontier_avoidance
    b.isCompact.isClosed s.isConnected.isPreconnected hdis with hin | hout
  · obtain ⟨B,hB,hball⟩ := s.exists_original_confined_ball he.compatible b hin
    exact ⟨B,hB.trans (interior_subset.trans hDR),hball⟩
  · have hER : closure (R \ D) ⊆ R := closure_minimal sdiff_subset hR.isClosed
    obtain ⟨B,hB,hball⟩ := hI.exists_ball_of_sphere_subset
      (hR.of_isClosed_subset isClosed_closure hER) s
      (fun x hx => subset_closure ⟨hSR hx,hout hx⟩)
    exact ⟨B,hB.trans hER,hball⟩

theorem HamiltonMarkedProtectedBall.contact_count_pos_of_nonbounding_sphere
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hI : IsPLIrreducible e (closure (latticeHandleDomain ι κ L \ D)))
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hn : ¬ ∃ B, B ⊆ latticeHandleDomain ι κ L ∧ Nonempty (ChartwisePLBall e B S))
    (Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (hp : HasDisjointPolygonPresentation
      (Q '' (S ∩ frontier (closure (latticeHandleDomain ι κ L \ D))))) :
    0 < Nat.card (ConnectedComponents
      (Q '' (S ∩ frontier (closure (latticeHandleDomain ι κ L \ D))))) := by
  by_contra hnpos
  have hz := (cocore_component_count_eq_zero_iff hp).mp (by omega)
  apply hn
  apply s.exists_ball_of_disjoint_ball_frontier he
    (isCompact_latticeHandleDomain ι κ L) b.ball b.subset_domain hI
    (hSR.trans interior_subset)
  apply disjoint_left.mpr
  intro x hxS hxD
  have hxE := (b.frontier_exterior_iff_interior he hdim hi (hSR hxS)).mpr hxD
  have hx : Q x ∈ Q '' (S ∩ frontier (closure (latticeHandleDomain ι κ L \ D))) :=
    ⟨x,⟨hxS,hxE⟩,rfl⟩
  simp only [hz,mem_empty_iff_false] at hx

theorem HamiltonMarkedProtectedBall.exists_nonbounding_sphere_exterior_position
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hI : IsPLIrreducible e (closure (latticeHandleDomain ι κ L \ D)))
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hn : ¬ ∃ B, B ⊆ latticeHandleDomain ι κ L ∧ Nonempty (ChartwisePLBall e B S)) :
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∃ (T : Set (LatticeHandleAmbient ι κ L))
      (Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
      (G : SimplicialComplex ℝ V3),
      Nonempty (ChartwisePLSphere e T) ∧ T ⊆ interior R ∧
      (¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B T)) ∧
      D ⊆ Q.source ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      T ∩ frontier E ⊆ Q.source ∧
      G.faces.Finite ∧ G.space = Q '' (T ∩ frontier E) ∧
      HasDisjointPolygonPresentation G.space ∧
      0 < Nat.card (ConnectedComponents G.space) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      (∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      ∀ w ∈ G.space, ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ C : OpenPartialHomeomorph V3 C3,
          w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
          (∀ z ∈ C.source, Q.symm z ∈ interior R) ∧ C w = 0 ∧
          LocallyPiecewiseAffineOn C C.source ∧
          LocallyPiecewiseAffineOn C.symm C.target ∧
          (∀ x ∈ C.source, Q.symm x ∈ T ↔ (C x).2 = 0) ∧
          ∀ x ∈ C.source, Q.symm x ∈ frontier E ↔ (C x).1.1 = 0 := by
  classical
  dsimp only
  obtain ⟨Q,Phi,G,hDQ,hQ,hfix,hPhi,hPhiinv,⟨s'⟩,hSR',hCQ,hG,hGs,hGc,hdegree,hcross⟩ :=
    b.exists_sphere_exterior_position he hdim hi s hSR
  have hn' : ¬ ∃ B, B ⊆ latticeHandleDomain ι κ L ∧
      Nonempty (ChartwisePLBall e B (Phi '' S)) := by
    rintro ⟨B,hB,⟨b'⟩⟩
    exact hn (b'.exists_ball_before_supported_motion Phi hB interior_subset
      hfix he.cover hPhiinv)
  let _ : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  have hcarrier := G.actual_edgeGraph_segmentCarrier_eq_space hGc
    (fun v => Set.nonempty_of_ncard_ne_zero (by rw [hdegree v]; omega))
  obtain ⟨n,P,hP,hunion,hpair⟩ :=
    G.vertexAbstractComplex.edgeGraph.exists_component_polygons_of_two_neighbors
      ((↑) : G.vertices → V3) hdegree Subtype.val_injective
      (fun {_ _ _ _} hvw hab => G.actual_edgeGraph_segment_intersection hvw hab)
  have hpres : HasDisjointPolygonPresentation G.space :=
    hasDisjointPolygonPresentation_of_family n P (fun i => ⟨(hP i).1,(hP i).2.1⟩)
      (hcarrier.symm.trans hunion) hpair
  have hpos := b.contact_count_pos_of_nonbounding_sphere he hdim hi hI s' hSR' hn' Q
    (hGs ▸ hpres)
  rw [←hGs] at hpos
  exact ⟨Phi '' S,Q,G,⟨s'⟩,hSR',hn',hDQ,hQ,hCQ,hG,hGs,hpres,hpos,hGc,hdegree,hcross⟩

open Classical in
theorem HamiltonMarkedProtectedBall.exists_minimal_nonbounding_sphere_exterior_position
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hI : IsPLIrreducible e (closure (latticeHandleDomain ι κ L \ D)))
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hn : ¬ ∃ B, B ⊆ latticeHandleDomain ι κ L ∧ Nonempty (ChartwisePLBall e B S)) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    let positions : Set (Set X × OpenPartialHomeomorph X V3 × SimplicialComplex ℝ V3) :=
      {d | Nonempty (ChartwisePLSphere e d.1) ∧ d.1 ⊆ interior R ∧
        (¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B d.1)) ∧
        D ⊆ d.2.1.source ∧
        (∀ i, (e i).symm.trans d.2.1 ∈ piecewiseAffineGroupoid V3) ∧
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
            ∀ x ∈ C.source, d.2.1.symm x ∈ frontier E ↔ (C x).1.1 = 0}
    ∃ d ∈ positions,
      0 < Nat.card (ConnectedComponents d.2.2.space) ∧
      (∀ d' ∈ positions, Nat.card (ConnectedComponents d.2.2.space) ≤
        Nat.card (ConnectedComponents d'.2.2.space)) ∧
      (∀ (A C : Set P2), IsFinitePLBallPair P2 A C → ∀ p : P2 → X,
        PolyhedralPLInCharts e p A → InjOn p A →
        p '' A ⊆ frontier D → p '' A ⊆ interior R →
        p '' A ∩ d.1 = p '' C → IsCompact ((d.1 ∩ frontier D) \ p '' C) →
        ∀ pole ∈ frontier D, pole ∉ p '' A → False) ∧
      (∃ (p : P2 → X) (m : ℕ) (n : Fin m → ℕ)
        (P : ∀ i, Polygon P2 (n i + 3)),
        PolyhedralPLInCharts e p (PLAnnularStrip.squareAnnulus 8 1) ∧
        InjOn p (PLAnnularStrip.squareAnnulus 8 1) ∧
        p '' (⋃ i, (P i).boundary ℝ) = d.1 ∩ frontier D ∧
        (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
        Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) ∧
        (∀ i x, x ∈ (P i).boundary ℝ →
          -1 < PLAnnularStrip.depth 8 x ∧ PLAnnularStrip.depth 8 x < 1) ∧
        p '' PLAnnularStrip.squareAnnulus 8 1 ⊆ frontier D ∧
        frontier D ∩ interior R ⊆ p '' PLAnnularStrip.squareAnnulus 8 1 ∧
        p '' {z | -1 < PLAnnularStrip.depth 8 z ∧ PLAnnularStrip.depth 8 z < 1}
          ⊆ interior R ∧
        (∀ z : PLAnnularStrip.squareAnnulus 8 1,
          p z ∈ frontier R ↔ PLAnnularStrip.depth 8 (z : P2) = -1 ∨
            PLAnnularStrip.depth 8 (z : P2) = 1) ∧
        (∀ i, Dehn.annulusSquare (8 : ℝ) 1 ⊆ (P i).inside) ∧
        ∀ i j, i ≠ j → closure (P i).inside ⊆ (P j).inside ∨
          closure (P j).inside ⊆ (P i).inside) ∧
      ∃ (K B : SimplicialComplex ℝ P2) (p : P2 → X),
        K.faces.Finite ∧ B ≤ K ∧
        PolyhedralPLInCharts e p K.space ∧ InjOn p K.space ∧
        p '' K.space = d.1 ∩ E ∧ p '' B.space = d.1 ∩ frontier E ∧
        (∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B.space) ∧
        (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
        (∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3) ∧
        (∀ t ∈ B.faces, t.card ≤ 2) ∧
        (∀ t ∈ K.faces, t.card = 2 →
          {q : Finset P2 | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
            if t ∈ B.faces then 1 else 2) ∧
        (∀ v ∈ K.vertices, IsConnected (K.link v).space) ∧
        HasDisjointPolygonPresentation B.space ∧
        Nat.card (ConnectedComponents B.space) = Nat.card (ConnectedComponents d.2.2.space) := by
  classical
  intro X R E positions
  have hex : ∃ n : ℕ, ∃ d ∈ positions,
      Nat.card (ConnectedComponents d.2.2.space) = n := by
    obtain ⟨T,Q,G,hs,hT,hnT,hDQ,hQ,hCQ,hG,hGs,hpres,hpos,hGc,hdegree,hcross⟩ :=
      b.exists_nonbounding_sphere_exterior_position he hdim hi hI s hSR hn
    exact ⟨_,(T,Q,G),⟨hs,hT,hnT,hDQ,hQ,hCQ,hG,hGs,hpres,hGc,hdegree,hcross⟩,rfl⟩
  obtain ⟨d,hd,hcount⟩ := Nat.find_spec hex
  have hnull : ∀ (A C : Set P2), IsFinitePLBallPair P2 A C → ∀ p : P2 → X,
      PolyhedralPLInCharts e p A → InjOn p A →
      p '' A ⊆ frontier D → p '' A ⊆ interior R →
      p '' A ∩ d.1 = p '' C → IsCompact ((d.1 ∩ frontier D) \ p '' C) →
      ∀ pole ∈ frontier D, pole ∉ p '' A → False := by
    intro A C hAC p hp hpi hpD hpR hpS hrem pole hpole hpoleout
    obtain ⟨⟨s'⟩,hSR',hn',hDQ,hQ,hCQ,hG,hGs,hpres,hGc,hdegree,hcross⟩ := hd
    have hFDQ : frontier D ⊆ d.2.1.source := b.ball.boundary_subset.trans hDQ
    have hcontacts (T : Set X) (hT : T ⊆ interior R) :
        T ∩ frontier E = T ∩ frontier D := by
      ext x
      exact and_congr_right (fun hx => b.frontier_exterior_iff_interior he hdim hi (hT hx))
    have hGsD : d.2.2.space = d.2.1 '' (d.1 ∩ frontier D) := hGs.trans
      (congrArg (fun U => d.2.1 '' U) (hcontacts d.1 hSR'))
    have hcrossD : ∀ w ∈ d.2.1 '' (d.1 ∩ frontier D),
        ∀ O : Set V3, IsOpen O → w ∈ O → ∃ C : OpenPartialHomeomorph V3 C3,
          w ∈ C.source ∧ C.source ⊆ O ∩ d.2.1.target ∧ C w = 0 ∧
          LocallyPiecewiseAffineOn C C.source ∧ LocallyPiecewiseAffineOn C.symm C.target ∧
          (∀ x ∈ C.source, d.2.1.symm x ∈ d.1 ↔ (C x).2 = 0) ∧
          ∀ x ∈ C.source, d.2.1.symm x ∈ frontier D ↔ (C x).1.1 = 0 := by
      intro w hw O hO hwO
      obtain ⟨Q,hwQ,hQO,hQR,hQ0,hQPL,hQiPL,hQS,hQE⟩ :=
        hcross w (hGsD.symm.subset hw) O hO hwO
      exact ⟨Q,hwQ,hQO,hQ0,hQPL,hQiPL,hQS,fun x hx =>
        (b.frontier_exterior_iff_interior he hdim hi (hQR x hx)).symm.trans (hQE x hx)⟩
    obtain ⟨t⟩ := b.ball.nonempty_boundarySphere
    obtain ⟨N,sN,hNR,hnN,hpresN,hsub,hlt,V,hV,hNV,hagree,hcrossN⟩ :=
      s'.exists_nonbounding_frontier_disk_step t (isCompact_latticeHandleDomain ι κ L)
        he hSR' (b.ball.boundary_subset.trans b.subset_domain) hn' d.2.1 hQ hFDQ
        (hGsD ▸ hpres) hcrossD hAC p hp hpi hpD hpR hpS hrem pole hpole hpoleout
    obtain ⟨H,hHG,hH,hHs,hHdegree⟩ := exists_contact_subcomplex_of_open_agreement
      s'.isCompact.isClosed sN.isCompact.isClosed isClosed_frontier d.2.1 hFDQ
      d.2.2 hG hGsD hV hNV hagree
    have hHsE : H.space = d.2.1 '' (N ∩ frontier E) := hHs.trans
      (congrArg (fun U => d.2.1 '' U) (hcontacts N hNR).symm)
    have hNQ : N ∩ frontier E ⊆ d.2.1.source := by
      rw [hcontacts N hNR]
      exact inter_subset_right.trans hFDQ
    have hposition : (N,d.2.1,H) ∈ positions := by
      refine ⟨⟨sN⟩,hNR,hnN,hDQ,hQ,hNQ,hH,hHsE,hHs.symm ▸ hpresN,
        fun a ha => hGc a (hHG ha),fun v => (hHdegree v).trans (hdegree _),?_⟩
      intro w hw O hO hwO
      obtain ⟨x,hx,rfl⟩ := hHs.subset hw
      have hxQ := hFDQ hx.2
      let W := O ∩ (d.2.1.target ∩ d.2.1.symm ⁻¹' interior R)
      have hW : IsOpen W := hO.inter (d.2.1.symm.isOpen_inter_preimage isOpen_interior)
      have hxW : d.2.1 x ∈ W := ⟨hwO,d.2.1.map_source hxQ,by
        change d.2.1.symm (d.2.1 x) ∈ interior R
        rw [d.2.1.left_inv hxQ]
        exact hNR hx.1⟩
      obtain ⟨C,hxC,hCW,hC0,hC,hCi,hCN,hCD⟩ :=
        hcrossN (d.2.1 x) ⟨x,hx,rfl⟩ W hW hxW
      refine ⟨C,hxC,fun z hz => ⟨(hCW hz).1.1,(hCW hz).2⟩,
        fun z hz => (hCW hz).1.2.2,hC0,hC,hCi,hCN,?_⟩
      intro z hz
      exact (b.frontier_exterior_iff_interior he hdim hi ((hCW hz).1.2.2)).trans (hCD z hz)
    have hle : Nat.card (ConnectedComponents d.2.2.space) ≤ Nat.card (ConnectedComponents H.space) :=
      hcount ▸ Nat.find_min' hex ⟨(N,d.2.1,H),hposition,rfl⟩
    rw [hGsD,hHs] at hle
    exact (not_lt_of_ge hle) hlt
  refine ⟨d,hd,?_,?_,?_,?_,?_⟩
  · obtain ⟨hs,hT,hnT,hDQ,hQ,hCQ,hG,hGs,hpres,hGc,hdegree,hcross⟩ := hd
    obtain ⟨s'⟩ := hs
    have hp := b.contact_count_pos_of_nonbounding_sphere he hdim hi hI s' hT hnT
      d.2.1 (hGs ▸ hpres)
    rwa [←hGs] at hp
  · intro d' hd'
    rw [hcount]
    exact Nat.find_min' hex ⟨d',hd',rfl⟩
  · exact hnull
  · obtain ⟨_,hT,_,hDQ,hQ,_,_,hGs,hpres,_⟩ := hd
    have hcontacts : d.1 ∩ frontier E = d.1 ∩ frontier D := by
      ext x
      exact and_congr_right (fun hx => b.frontier_exterior_iff_interior he hdim hi (hT hx))
    have hpD : HasDisjointPolygonPresentation (d.2.1 '' (d.1 ∩ frontier D)) := by
      rw [←hcontacts,←hGs]
      exact hpres
    obtain ⟨p,m,n,P,hp,hpi,hcover,hP,hdis,hstrict,hfront,hfull,hint,hends,halt⟩ :=
      b.exists_original_annular_contact_alternatives he hdim hi d.2.1 hQ hDQ hT hpD
    rcases halt with ⟨i,hdisk,hpd,hpid,hbody,hcontact,hrem,pole,hpole,hout⟩ | hess
    · exact (hnull _ _ hdisk p hpd hpid (hbody.trans inter_subset_left)
        (hbody.trans inter_subset_right) hcontact hrem pole hpole.1 hout).elim
    · exact ⟨p,m,n,P,hp,hpi,hcover,hP,hdis,hstrict,hfront,hfull,hint,hends,hess⟩
  · obtain ⟨⟨s'⟩,hT,hnT,hDQ,hQ,hCQ,hG,hGs,hpres,hGc,hdegree,hcross⟩ := hd
    have hphysical : ∀ w ∈ d.2.1 '' (d.1 ∩ frontier E),
        ∃ C : OpenPartialHomeomorph V3 C3,
          w ∈ C.source ∧ C w = 0 ∧ LocallyPiecewiseAffineOn C C.source ∧
          (∀ x ∈ C.source, d.2.1.symm x ∈ d.1 ↔ (C x).2 = 0) ∧
          ∀ x ∈ C.source, d.2.1.symm x ∈ frontier E ↔ (C x).1.1 = 0 := by
      intro w hw
      obtain ⟨C,hwC,_,_,hC0,hC,_,hCS,hCE⟩ :=
        hcross w (hGs.symm.subset hw) univ isOpen_univ (mem_univ w)
      exact ⟨C,hwC,hC0,hC,hCS,hCE⟩
    have hmodel := b.exists_nonbounding_exterior_surface he hdim hi hI s' hT hnT
      d.2.1 hQ hCQ hphysical
    have hGs' : d.2.2.space = d.2.1 ''
        (d.1 ∩ frontier (closure (latticeHandleDomain ι κ L \ D))) := hGs
    dsimp only at hmodel
    rw [←hGs'] at hmodel
    exact hmodel

end PoincareConjecture.M76
