import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.SurfaceIntersectionCrossings
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalCapNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.NestedFiniteSphereCut
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalSphereChartCarrier
import PoincareConjecture.Proofs.M76.PrimeReduction.SphereAmbientTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.MovedClippedSphereDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.SurfaceIntersectionDegree
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.ClosedSetProtectedSurfacePosition
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartSurfaceMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Coordinate.IntersectionGraph









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLBall.exists_enclosing_surface_window
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D B R S : Set X}
    (b : ChartwisePLBall e D B) (hR : IsCompact R) (he : PLDomain e R)
    (hDR : D ⊆ R) (s : ChartwisePLSphere e S) :
    ∃ (Q : OpenPartialHomeomorph X V3)
      (J P T : SimplicialComplex ℝ V3),
      D ⊆ Q.source ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      J.faces.Finite ∧ Convex ℝ J.space ∧ J.space ⊆ Q.target ∧
      Q '' D ⊆ interior J.space ∧
      P.faces.Finite ∧ P.space = Q '' (S ∩ Q.source) ∩ J.space ∧
      (∀ a ∈ P.faces, a.card ≤ 3) ∧
      (∀ x ∈ J.space, Q.symm x ∈ S ↔ x ∈ P.space) ∧
      T.faces.Finite ∧ T.space = Q '' B ∧ T.space ⊆ interior J.space ∧
      (∀ a ∈ T.faces, a.card ≤ 3) := by
  obtain ⟨N,hN,hRN,heN⟩ := he.exists_compact_ambient_neighborhood hR
  obtain ⟨Q,hDQ,_,hQt,hQ⟩ := b.exists_enclosing_chart_in_domain hN heN
    (hDR.trans hRN) isOpen_univ (subset_univ D)
  have hD : IsCompact D := isCompact_iff_compactSpace.mpr b.parametrization.compactSpace
  have hQD : IsCompact (Q '' D) := hD.image_of_continuousOn (Q.continuousOn.mono hDQ)
  have hQDb : Q '' D ⊆ ball (0 : V3) 1 := by
    rintro _ ⟨x,hx,rfl⟩
    exact hQt ▸ Q.map_source (hDQ hx)
  obtain ⟨r,⟨hr,hr1⟩,hDr⟩ := exists_pos_lt_subset_ball zero_lt_one hQD.isClosed hQDb
  obtain ⟨J,hJ,hJs⟩ := SimplicialComplex.exists_finite_coordinate_closedBall (0 : V3) hr.le
  have hJQ : J.space ⊆ Q.target := by
    rw [hJs,hQt]
    exact closedBall_subset_ball hr1
  have hDJ : Q '' D ⊆ interior J.space := by
    rw [hJs]
    exact hDr.trans ball_subset_interior_closedBall
  obtain ⟨P,hP,hPs,hPc,hlocal⟩ := s.exists_finite_chart_carrier Q hQ J hJ hJQ
  obtain ⟨sb⟩ := b.nonempty_boundarySphere
  obtain ⟨T,hT,hTs,hTc,_⟩ := sb.exists_finite_chart_carrier Q hQ J hJ hJQ
  have hTwhole : T.space = Q '' B := by
    rw [hTs,inter_eq_left.mpr (b.boundary_subset.trans hDQ)]
    exact inter_eq_left.mpr ((image_mono b.boundary_subset).trans
      (hDJ.trans interior_subset))
  exact ⟨Q,J,P,T,hDQ,hQ,hJ,hJs.symm ▸ convex_closedBall _ _,hJQ,hDJ,
    hP,hPs,hPc,hlocal,hT,hTwhole,hTwhole.symm ▸
      (image_mono b.boundary_subset).trans hDJ,hTc⟩

theorem ChartwisePLBall.exists_protected_frontier_intersection_graph_with_crossings
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D B R S : Set X}
    (b : ChartwisePLBall e D B) (hR : IsCompact R) (he : PLDomain e R)
    (hDR : D ⊆ R) (s : ChartwisePLSphere e S) (hSR : S ⊆ interior R) :
    ∃ (Q : OpenPartialHomeomorph X V3) (Phi : X ≃ₜ X)
      (G : SimplicialComplex ℝ V3),
      D ⊆ Q.source ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      EqOn Phi id (interior R)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (Phi '' S)) ∧ Phi '' S ⊆ interior R ∧
      G.faces.Finite ∧ G.space = Q '' (Phi '' S ∩ B) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      (∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      ∀ w ∈ G.space, ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ C : OpenPartialHomeomorph V3 ((ℝ × ℝ) × ℝ),
          w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧ C w = 0 ∧
          LocallyPiecewiseAffineOn C C.source ∧
          LocallyPiecewiseAffineOn C.symm C.target ∧
          (∀ x ∈ C.source, Q.symm x ∈ Phi '' S ↔ (C x).2 = 0) ∧
          ∀ x ∈ C.source, Q.symm x ∈ B ↔ (C x).1.1 = 0 := by
  classical
  obtain ⟨Q,J,P,T,hDQ,hQ,hJ,hcv,hJQ,hDJ,hP,hPs,hPc,hlocal,hT,hTs,hTJ,hTc⟩ :=
    b.exists_enclosing_surface_window hR he hDR s
  let C := J.frontierSubcomplex J.space
  have hC : C.faces.Finite := J.frontierSubcomplex_finite _ hJ
  have hne : (interior J.space).Nonempty := by
    have hDne : D.Nonempty := by
      let z : closedBall (0 : V3) 1 := ⟨0,mem_closedBall_self zero_le_one⟩
      exact ⟨b.parametrization z,(b.parametrization z).property⟩
    obtain ⟨x,hx⟩ := hDne
    exact ⟨Q x,hDJ (mem_image_of_mem Q hx)⟩
  have hCs : C.space = frontier J.space := J.frontierSubcomplex_space
    (J.isCompact_space_of_finite hJ).isClosed hcv hne rfl
  obtain ⟨P0,hP0,hP0s⟩ := P.exists_finite_triangulation_inter C hP hC
  rw [hCs] at hP0s
  have hPJ : P.space ⊆ J.space := hPs.subset.trans inter_subset_right
  have hP0P : P0.space ⊆ P.space := hP0s.subset.trans inter_subset_left
  have hd : Disjoint P0.space T.space := by
    apply disjoint_left.mpr
    intro x hx hxT
    exact (hP0s.subset hx).2.2 (hTJ hxT)
  let Z := Q '' ((interior R)ᶜ ∩ Q.symm '' J.space)
  have hwindow : IsCompact (Q.symm '' J.space) :=
    (J.isCompact_space_of_finite hJ).image_of_continuousOn (Q.symm.continuousOn.mono hJQ)
  have hZsource : (interior R)ᶜ ∩ Q.symm '' J.space ⊆ Q.source := by
    rintro _ ⟨_,z,hz,rfl⟩
    exact Q.map_target (hJQ hz)
  have hZ : IsClosed Z := ((hwindow.inter_left isOpen_interior.isClosed_compl).image_of_continuousOn
    (Q.continuousOn.mono hZsource)).isClosed
  have hnear : ∀ x : P.space, (x : V3) ∈ Z →
      (Subtype.val ⁻¹' P0.space : Set P.space) ∈ nhds x := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hx
    have hyS : y ∈ S := by
      have hh := (hlocal x (hPJ x.property)).mpr x.property
      rw [←hxy,Q.left_inv (hZsource hy)] at hh
      exact hh
    exact False.elim (hy.1 (hSR hyS))
  obtain ⟨H,A,hA,hAs,hAc,hpos,hvert,hedge,hcontacts,hHZ,hHU⟩ :=
    SimplicialComplex.exists_closed_set_protected_surface_edge_position (by simp)
      J P P0 T hJ hP hP0 hT hcv hP0P hPJ hP0s.symm.subset hZ hnear hPc
      (hd.mono_right T.vertices_subset_space)
      (fun t ht _ => by
        rw [(hd.mono_right (T.convexHull_subset_space ht)).inter_eq]
        exact finite_empty) (by norm_num : (0:ℝ)<1)
  obtain ⟨Phi,hcoord,hout,_,hPhi,hPhiinv,himage⟩ :=
    exists_original_chart_surface_motion e he.compatible Q hQ J hJ hJQ
      (hP0P.trans hPJ) H S P.space hlocal
  have hfix : EqOn Phi id (interior R)ᶜ := by
    intro x hx
    by_cases hxW : x ∈ Q.symm '' J.space
    · obtain ⟨z,hz,rfl⟩ := hxW
      rw [hcoord z (hJQ hz)]
      have hzZ : z ∈ Z := ⟨Q.symm z,⟨hx,⟨z,hz,rfl⟩⟩,Q.right_inv (hJQ hz)⟩
      rw [hHZ 1 hzZ]
      rfl
    · exact hout hxW
  obtain ⟨G,hG,hGs,hGc⟩ :=
    SimplicialComplex.exists_surface_intersection_graph_of_position (by simp)
      A T hA hT hAc hTc (Z:=P0.space) ∅ (by simp)
      (fun x hx => False.elim (disjoint_left.mp hd hx.1 hx.2)) hpos
  have hSimage : Phi '' S ⊆ interior R := by
    rintro _ ⟨x,hx,rfl⟩
    by_contra hn
    have hh : Phi x = x := Phi.injective (hfix hn)
    exact hn (hh.symm ▸ hSR hx)
  have hdegree (v : G.vertices) :
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := by
    apply SimplicialComplex.ncard_surface_intersection_neighbors_of_local_disks
      A T G hA hT hG hAc hTc hGc hGs hd hpos
    · intro w hw
      exact s.exists_moved_clipped_disk_neighborhood Q hQ J P A hJ hJQ hP hPs
        H hAs hw.1 (hTJ hw.2)
    · intro w hw
      obtain ⟨sb⟩ := b.nonempty_boundarySphere
      have hTcarrier : T.space = Q '' (B ∩ Q.source) ∩ J.space := by
        rw [inter_eq_left.mpr (b.boundary_subset.trans hDQ),←hTs]
        exact (inter_eq_left.mpr (hTJ.trans interior_subset)).symm
      exact sb.exists_clipped_disk_neighborhood Q hQ J T hJ hJQ hT hTcarrier hw.2 (hTJ hw.2)
  refine ⟨Q,Phi,G,hDQ,hQ,hfix,hPhi,hPhiinv,s.nonempty_image Phi he.cover hPhi,
    hSimage,hG,?_,hGc,hdegree,?_⟩
  · rw [hGs,hTs]
    ext z
    constructor
    · rintro ⟨hzA,x,hxB,hxz⟩
      have hzJ : z ∈ J.space := interior_subset (hTJ (hTs.symm ▸ ⟨x,hxB,hxz⟩))
      refine ⟨x,⟨?_,hxB⟩,hxz⟩
      have hh := (himage z hzJ).mpr (hAs ▸ hzA)
      rw [←hxz,Q.left_inv (hDQ (b.boundary_subset hxB))] at hh
      exact hh
    · rintro ⟨x,⟨hxS,hxB⟩,rfl⟩
      have hxJ := interior_subset (hDJ (mem_image_of_mem Q (b.boundary_subset hxB)))
      refine ⟨?_,⟨x,hxB,rfl⟩⟩
      rw [hAs]
      apply (himage (Q x) hxJ).mp
      simpa only [Q.left_inv (hDQ (b.boundary_subset hxB))] using hxS

  · intro w hw O hO hwO
    have hwAT := hGs.subset hw
    have hdiskA := s.exists_moved_clipped_disk_neighborhood Q hQ J P A hJ hJQ hP hPs
      H hAs hwAT.1 (hTJ hwAT.2)
    obtain ⟨sb⟩ := b.nonempty_boundarySphere
    have hTcarrier : T.space = Q '' (B ∩ Q.source) ∩ J.space := by
      rw [inter_eq_left.mpr (b.boundary_subset.trans hDQ),←hTs]
      exact (inter_eq_left.mpr (hTJ.trans interior_subset)).symm
    have hdiskT := sb.exists_clipped_disk_neighborhood Q hQ J T hJ hJQ hT hTcarrier
      hwAT.2 (hTJ hwAT.2)
    obtain ⟨C,hwC,hCO,hCw,hC,hCi,hCA,hCT⟩ :=
      A.exists_surface_crossing_chart_of_position T hA hT hAc hTc hd hpos hwAT
        hdiskA hdiskT (hO.inter isOpen_interior) ⟨hwO,hTJ hwAT.2⟩
    refine ⟨C,hwC,fun x hx => ⟨(hCO hx).1,hJQ (interior_subset (hCO hx).2)⟩,
      hCw,hC,hCi,?_,?_⟩
    · intro x hx
      exact ((himage x (interior_subset (hCO hx).2)).trans
        (Set.ext_iff.mp hAs x).symm).trans (hCA x hx)
    · intro x hx
      have hxQ := hJQ (interior_subset (hCO hx).2)
      have hmem : Q.symm x ∈ B ↔ x ∈ T.space := by
        rw [hTs]
        constructor
        · intro hh
          exact ⟨Q.symm x,hh,Q.right_inv hxQ⟩
        · rintro ⟨y,hy,hxy⟩
          rw [←hxy,Q.left_inv (hDQ (b.boundary_subset hy))]
          exact hy
      exact hmem.trans (hCT x hx)
theorem ChartwisePLBall.exists_protected_frontier_intersection_graph_with_degree
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D B R S : Set X}
    (b : ChartwisePLBall e D B) (hR : IsCompact R) (he : PLDomain e R)
    (hDR : D ⊆ R) (s : ChartwisePLSphere e S) (hSR : S ⊆ interior R) :
    ∃ (Q : OpenPartialHomeomorph X V3) (Phi : X ≃ₜ X)
      (G : SimplicialComplex ℝ V3),
      D ⊆ Q.source ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      EqOn Phi id (interior R)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (Phi '' S)) ∧ Phi '' S ⊆ interior R ∧
      G.faces.Finite ∧ G.space = Q '' (Phi '' S ∩ B) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := by
  obtain ⟨Q,Phi,G,hDQ,hQ,hfix,hPhi,hPhiinv,hSphere,hS,hG,hGs,hGc,hdegree,_⟩ :=
    b.exists_protected_frontier_intersection_graph_with_crossings hR he hDR s hSR
  exact ⟨Q,Phi,G,hDQ,hQ,hfix,hPhi,hPhiinv,hSphere,hS,hG,hGs,hGc,hdegree⟩

theorem ChartwisePLBall.exists_protected_frontier_intersection_graph
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D B R S : Set X}
    (b : ChartwisePLBall e D B) (hR : IsCompact R) (he : PLDomain e R)
    (hDR : D ⊆ R) (s : ChartwisePLSphere e S) (hSR : S ⊆ interior R) :
    ∃ (Q : OpenPartialHomeomorph X V3) (Phi : X ≃ₜ X)
      (G : SimplicialComplex ℝ V3),
      D ⊆ Q.source ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      EqOn Phi id (interior R)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (Phi '' S)) ∧ Phi '' S ⊆ interior R ∧
      G.faces.Finite ∧ G.space = Q '' (Phi '' S ∩ B) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) := by
  obtain ⟨Q,Phi,G,hDQ,hQ,hfix,hPhi,hPhiinv,hSphere,hS,hG,hGs,hGc,_⟩ :=
    b.exists_protected_frontier_intersection_graph_with_degree hR he hDR s hSR
  exact ⟨Q,Phi,G,hDQ,hQ,hfix,hPhi,hPhiinv,hSphere,hS,hG,hGs,hGc⟩

end PoincareConjecture.M76
