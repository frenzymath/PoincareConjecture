import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.FaceGraphComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ActualFaceComponents
import PoincareConjecture.Proofs.M76.Mathlib.InnermostPolygonDisk
import PoincareConjecture.Proofs.M76.Mathlib.PolygonConvexContainment
import PoincareConjecture.Proofs.M76.Mathlib.ConvexIntrinsicInterior
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalTriangleReturningBigons
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)



theorem exists_innermost_face_circle_disk_in_slice
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hdim : ∀ s ∈ G.faces, s.card ≤ 2)
    (t : Finset V3) (ht : t.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : t → V3))
    (hsub : G.space ⊆ convexHull ℝ (t : Set V3))
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set V3))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
    (hRF : Function.LeftInverse R F)
    (hFR : EqOn (F ∘ R) id (convexHull ℝ (t : Set V3)))
    (hcircle : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (t : Set V3)) = ∅) :
    ∃ (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (n : ℕ) (P : Polygon P2 (n + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
      F '' P.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
      IsFinitePLBallPair P2 (F '' closure P.inside) (F '' P.boundary ℝ) ∧
      IsCompact (F '' closure P.inside) ∧
      F '' closure P.inside ⊆ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)) ∧
      (F '' closure P.inside) ∩ G.space = F '' P.boundary ℝ := by
  classical
  let H := G.vertexAbstractComplex.edgeGraph
  let B : H.ConnectedComponent → Set V3 := fun C =>
    C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
  let T := convexHull ℝ (t : Set V3)
  let I := {C : H.ConnectedComponent // B C ∩ intrinsicFrontier ℝ T = ∅}
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  let : Nonempty I := ⟨⟨hcircle.choose, hcircle.choose_spec⟩⟩
  obtain ⟨hwhole, hdis, hclass⟩ := G.exists_actual_face_components hG hdim
    t ht hind hsub hfinite hinterior hexterior
  have hBT (C : H.ConnectedComponent) : B C ⊆ T := by
    intro x hx
    apply hsub
    rw [hwhole]
    exact mem_iUnion.mpr ⟨C, hx⟩
  have hRi : InjOn R T := by
    intro x hx y hy hxy
    exact (hFR hx).symm.trans ((congrArg F hxy).trans (hFR hy))
  have hno (x : V3) (hx : x ∈ intrinsicFrontier ℝ T) :
      x ∉ intrinsicInterior ℝ T := by
    rw [← closure_sdiff_intrinsicInterior] at hx
    exact hx.2
  have hpoly (i : I) : ∃ (n : ℕ) (P : Polygon P2 (n + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ = R '' B i.val ∧
        P.boundary ℝ ⊆ R '' intrinsicInterior ℝ T := by
    rcases hclass i.val with ⟨n, e, _, _, hrim, _⟩ | ⟨n, P, hi, hP, hPB, hPT⟩
    · have hx : ((e 0).val : V3) ∈ B i.val ∩ intrinsicFrontier ℝ T :=
        hrim.symm.subset (by simp)
      exact (Set.notMem_empty _ (i.property ▸ hx)).elim
    · have hleft : LeftInvOn F R (P.boundary ℝ) :=
        fun x hx => hFR (hBT i.val (hPB.subset hx))
      obtain ⟨hinj, hedges, _⟩ := P.affineImage_of_leftInvOn hP hi
        R.toAffineMap F.toAffineMap hleft
      refine ⟨n, P.affineImage R.toAffineMap, hinj, hedges, ?_, ?_⟩
      · rw [P.affineImage_boundary, hPB]
        rfl
      · rw [P.affineImage_boundary]
        exact image_mono hPT
  choose n P hi hP hPB hPT using hpoly
  have hPdis : Pairwise fun i j : I => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ) := by
    intro i j hij
    rw [hPB i, hPB j]
    exact (hdis (fun h => hij (Subtype.ext h))).image hRi (hBT i.val) (hBT j.val)
  obtain ⟨i, hball, hcircles, _⟩ :=
    Polygon.exists_innermost_finitePL_disk n P hP hi hPdis
  have hDT : closure (P i).inside ⊆ R '' intrinsicInterior ℝ T :=
    (P i).closure_inside_subset_convex (hP i) (hi i)
      ((convex_convexHull ℝ (t : Set V3)).intrinsicInterior.affine_image R.toAffineMap)
      (by rintro _ ⟨j, rfl⟩; exact hPT i ((P i).vertex_mem_boundary j))
  have hFDT : F '' closure (P i).inside ⊆ intrinsicInterior ℝ T := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hDT hx
    have heq : F (R y) = y := hFR (intrinsicInterior_subset hy)
    rw [heq]
    exact hy
  have hFPB (j : I) : F '' (P j).boundary ℝ = B j.val := by
    rw [hPB j, ← image_comp]
    exact (image_congr (hFR.mono (hBT j.val))).trans (image_id _)
  have havoid (C : H.ConnectedComponent) (hCi : C ≠ i.val) :
      Disjoint (closure (P i).inside) (R '' B C) := by
    have hbd : Disjoint ((P i).boundary ℝ) (R '' B C) := by
      rw [hPB i]
      exact (hdis (Ne.symm hCi)).image hRi (hBT i.val) (hBT C)
    by_cases hC : B C ∩ intrinsicFrontier ℝ T = ∅
    · let j : I := ⟨C, hC⟩
      apply disjoint_left.mpr
      intro x hxD hxB
      have hxP : x ∈ (P j).boundary ℝ := (hPB j).symm.subset hxB
      exact disjoint_left.mp hbd
        (hcircles.subset ⟨hxD, mem_iUnion.mpr ⟨j, hxP⟩⟩) hxB
    · rcases hclass C with ⟨m, e, _, hinterval, hrim, _⟩ | ⟨m, Q, hQi, hQ, hQB, hQT⟩
      · have hboundary : Disjoint (frontier (P i).inside) (R '' B C) := by
          rw [(P i).frontier_inside (hP i) (hi i)]
          exact hbd
        have hout : Disjoint (P i).inside (R '' B C) := by
          apply disjoint_left.mpr
          intro x hxD hxB
          have hconn : IsPreconnected (R '' B C) :=
            hinterval.isConnected.isPreconnected.image R R.continuous.continuousOn
          have hBC : R '' B C ⊆ (P i).inside :=
            hconn.m76_subset_of_disjoint_frontier
              ((P i).isOpen_inside (hP i) (hi i)) hboundary ⟨x, hxB, hxD⟩
          have hy : ((e 0).val : V3) ∈ B C ∩ intrinsicFrontier ℝ T :=
            hrim.symm.subset (by simp)
          have hyy := hFDT (mem_image_of_mem F (subset_closure
            (hBC (mem_image_of_mem R hy.1))))
          have heq : F (R ((e 0).val : V3)) = ((e 0).val : V3) := hFR (hBT C hy.1)
          rw [heq] at hyy
          exact hno _ hy.2 hyy
        apply disjoint_left.mpr
        intro x hxD hxB
        rw [closure_eq_self_union_frontier, (P i).frontier_inside (hP i) (hi i)] at hxD
        exact hxD.elim (fun hx => disjoint_left.mp hout hx hxB)
          (fun hx => disjoint_left.mp hbd hx hxB)
      · exfalso
        apply hC
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hno _ hx.2 (hQT (hQB.symm.subset hx.1))
  refine ⟨i.val, n i, P i, hi i, hP i, hFPB i,
    hball.affine_image F hRF.injective.injOn,
    ((P i).isCompact_closure_inside (hP i) (hi i)).image F.continuous, hFDT, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨⟨y, hy, rfl⟩, hxG⟩
    obtain ⟨C, hxC⟩ := mem_iUnion.mp (hwhole.subset hxG)
    by_cases hCi : C = i.val
    · exact (hFPB i).symm.subset (hCi ▸ hxC)
    · have hyC : y ∈ R '' B C := ⟨F y, hxC, hRF y⟩
      exact (disjoint_left.mp (havoid C hCi) hy hyC).elim
  · intro x hx
    refine ⟨image_mono hball.1 hx, ?_⟩
    rw [hwhole]
    exact mem_iUnion.mpr ⟨i.val, (hFPB i).subset hx⟩



theorem exists_original_triangle_innermost_circle_disk
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hsub : G.space ⊆ convexHull ℝ (A '' (s : Set E)))
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (hcircle : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅) :
    ∃ (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
      (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (n : ℕ) (P : Polygon P2 (n + 3)),
      Function.LeftInverse R F ∧ Function.Injective P ∧ P.HasSimplicialEdges ∧
      F '' P.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
      IsFinitePLBallPair P2 (F '' closure P.inside) (F '' P.boundary ℝ) ∧
      IsCompact (F '' closure P.inside) ∧
      F '' closure P.inside ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) ∧
      (F '' closure P.inside) ∩ G.space = F '' P.boundary ℝ := by
  classical
  let K₀ : SimplicialComplex ℝ E :=
    { faces := {b | b ∈ K.faces ∧ b ⊆ s}
      indep := fun hb => K.indep hb.1
      isRelLowerSet_faces := by
        intro b hb
        exact ⟨K.nonempty_of_mem_faces hb.1, fun c hcb hc =>
          ⟨K.down_closed hb.1 hcb hc, hcb.trans hb.2⟩⟩
      inter_subset_convexHull := fun hb hc => K.inter_subset_convexHull hb.1 hc.1 }
  have hs₀ : s ∈ K₀.faces := ⟨hs, Finset.Subset.rfl⟩
  have hK₀s : K₀.space = convexHull ℝ (s : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨b, hb, hxb⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact convexHull_mono hb.2 hxb
    · exact K₀.convexHull_subset_space hs₀
  have hAi : InjOn A K₀.space := by
    intro x hx y hy hxy
    have hx' := hK₀s.subset hx
    have hy' := hK₀s.subset hy
    exact hgi (K.convexHull_subset_space hs hx') (K.convexHull_subset_space hs hy')
      (Q.injOn (hmap hx') (hmap hy') ((hA hx').trans (hxy.trans (hA hy').symm)))
  have hf : K₀.AffineOnFaces A := K₀.affineOnFaces_affine A
  let T := hf.embeddedImage hAi
  have ht : s.image A ∈ T.faces :=
    (hf.image_mem_embeddedImage_iff hAi (K₀.subset_space hs₀)).mpr hs₀
  have ht3 : (s.image A).card = 3 := by
    rw [Finset.card_image_of_injOn (hAi.mono (K₀.subset_space hs₀)), hs3]
  obtain ⟨v0, v1, v2, h01, h02, h12, hverts⟩ := Finset.card_eq_three.mp ht3
  have hface : ({v0, v1, v2} : Set V3) = A '' (s : Set E) := by
    simpa only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton] using
      (congrArg (fun t : Finset V3 => (t : Set V3)) hverts).symm
  obtain ⟨F, R, hRF, hFR, _, _, _, _, _, _, _⟩ :=
    T.exists_returning_face_coordinates h01 h02 h12 (by
      convert ht using 1
      ext x
      simp only [hverts, Finset.mem_insert, Finset.mem_singleton])
  have hFR' : EqOn (F ∘ R) id (convexHull ℝ ((s.image A : Finset V3) : Set V3)) := by
    rw [Finset.coe_image]
    exact hFR.mono (fun x hx => convexHull_subset_affineSpan _ (hface.symm ▸ hx))
  obtain ⟨C, n, P, hi, hP, hPB, hball, hcompact, hinter, hexact⟩ :=
    exists_innermost_face_circle_disk_in_slice G hG hdim (s.image A)
      (T.nonempty_of_mem_faces ht) (T.indep ht)
      (by simpa only [Finset.coe_image] using hsub)
      (by simpa only [Finset.coe_image] using hfinite)
      (by simpa only [Finset.coe_image] using hinterior)
      (by simpa only [Finset.coe_image] using hexterior) F R hRF hFR'
      (by simpa only [Finset.coe_image] using hcircle)
  exact ⟨F, R, C, n, P, hRF, hi, hP, hPB, hball, hcompact,
    by simpa only [Finset.coe_image] using hinter, hexact⟩



theorem exists_original_face_circle_cap
    {E X κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K N : SimplicialComplex ℝ E) (hNK : N ≤ K)
    (g : E → X) (hgi : InjOn g K.space)
    {Z : Set X} (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3) (hsN : s ∉ N.faces)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (J M G : SimplicialComplex ℝ V3)
    (htriangleJ : convexHull ℝ (A '' (s : Set E)) ⊆ J.space)
    (hJQ : J.space ⊆ Q.target) (hG : G.faces.Finite)
    (hGs : G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)))
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (S : κ → Set X) (Phi : X ≃ₜ X)
    (hPhiS : ∀ x ∈ J.space, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ x ∈ M.space)
    (hmembers : ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      ∃! i, Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ Phi '' S i)
    (hcircle : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅) :
    ∃ (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (n : ℕ) (L : Polygon V3 (n + 3)) (D : Set V3) (i : κ),
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
      IsFinitePLBallPair P2 D (L.boundary ℝ) ∧ IsCompact D ∧
      D ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) ∧
      D ∩ G.space = L.boundary ℝ ∧
      IsCompact (Q.symm '' D) ∧
      Q.symm '' D ⊆ g '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
      Disjoint (Q.symm '' D) Z ∧
      Disjoint (Q.symm '' D) (⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
        g '' convexHull ℝ (a : Set E)) ∧
      (Q.symm '' D) ∩ Phi '' (⋃ j, S j) = Q.symm '' L.boundary ℝ ∧
      Q.symm '' L.boundary ℝ ⊆ Phi '' S i ∧
      (∀ j, Q.symm '' L.boundary ℝ ⊆ Phi '' S j → j = i) := by
  classical
  obtain ⟨F, R, C, n, P, hRF, hi, hP, hPB, hball, hcompact, hDT, hexact⟩ :=
    exists_original_triangle_innermost_circle_disk K g hgi hs hs3 Q A hmap hA
      G hG hdim (fun _ hx => (hGs.subset hx).2) hfinite hinterior hexterior hcircle
  let L := P.affineImage F.toAffineMap
  let D := F '' closure P.inside
  have hLB : L.boundary ℝ = F '' P.boundary ℝ := P.affineImage_boundary F.toAffineMap
  have hLi : Function.Injective L := hRF.injective.comp hi
  have hL : L.HasSimplicialEdges :=
    P.hasSimplicialEdges_affineImage hP F.toAffineMap hRF.injective
  have hLD : L.boundary ℝ ⊆ D := hLB.trans_subset hball.1
  have hDQ : D ⊆ Q.target := fun x hx => hJQ (htriangleJ (intrinsicInterior_subset (hDT hx)))
  have hDphys : IsCompact (Q.symm '' D) :=
    hcompact.image_of_continuousOn (Q.symm.continuousOn.mono hDQ)
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro u hu v hv huv
    exact hgi (K.convexHull_subset_space hs hu) (K.convexHull_subset_space hs hv)
      (Q.injOn (hmap hu) (hmap hv) ((hA hu).trans (huv.trans (hA hv).symm)))
  have hAsp := A.toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) (K.nonempty_of_mem_faces hs).to_set.convexHull hAi
  have hrel : intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) =
      A '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    change intrinsicInterior ℝ (convexHull ℝ (A.toAffineMap '' (s : Set E))) =
      A.toAffineMap '' intrinsicInterior ℝ (convexHull ℝ (s : Set E))
    rw [← A.toAffineMap.image_convexHull,
      A.toAffineMap.intrinsicInterior_image_of_injOn_span _ hAsp]
  have hphysical : Q.symm '' D ⊆ g '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hrel.subset (hDT hx)
    refine ⟨u, hu, ?_⟩
    rw [← hA (intrinsicInterior_subset hu)]
    exact (Q.left_inv (hmap (intrinsicInterior_subset hu))).symm
  have hDZ : Disjoint (Q.symm '' D) Z := by
    apply disjoint_left.mpr
    intro x hx hxZ
    obtain ⟨u, hu, rfl⟩ := hphysical hx
    exact hsN ((SimplicialComplex.mem_subcomplex_of_mem_intrinsicInterior_iff hNK hs hu).mp
      ((hmark u (K.convexHull_subset_space hs (intrinsicInterior_subset hu))).mp hxZ))
  have hDsk : Disjoint (Q.symm '' D) (⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
      g '' convexHull ℝ (a : Set E)) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxsk
    have hfront := original_skeleton_triangle_intersection_subset_boundary K g hgi hs hs3
      Q A hmap hA (intrinsicInterior_subset (hDT hx)) hxsk
    rw [← closure_sdiff_intrinsicInterior] at hfront
    exact hfront.2 (hDT hx)
  have hwhole : (Q.symm '' D) ∩ Phi '' (⋃ j, S j) = Q.symm '' L.boundary ℝ := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxS⟩
      have hxM := (hPhiS x (htriangleJ (intrinsicInterior_subset (hDT hx)))).mp hxS
      have hxG := hGs.symm.subset ⟨hxM, intrinsicInterior_subset (hDT hx)⟩
      exact ⟨x, hLB.symm.subset (hexact.subset ⟨hx, hxG⟩), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxD := hLD hx
      have hxG := (hexact.symm.subset (hLB.subset hx)).2
      exact ⟨⟨x, hxD, rfl⟩,
        (hPhiS x (htriangleJ (intrinsicInterior_subset (hDT hxD)))).mpr (hGs.subset hxG).1⟩
  obtain ⟨i, hiS, hiunique⟩ := hmembers C
  have hLC : L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) :=
    hLB.trans hPB
  refine ⟨C, n, L, D, i, hLi, hL, hLC, ?_, hcompact, hDT, ?_, hDphys,
    hphysical, hDZ, hDsk, hwhole, ?_, ?_⟩
  · rwa [hLB]
  · exact hexact.trans hLB.symm
  · rwa [hLC]
  · intro j hj
    exact hiunique j (by rwa [← hLC])




theorem exists_original_sphere_system_innermost_circle_disk
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z)
    (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    (hSZ : Disjoint (⋃ i, S i) Z) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (J M G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) (W : Set X),
      J.faces.Finite ∧ J.space ⊆ Q.target ∧
      convexHull ℝ (A '' (s : Set E)) ⊆ interior J.space ∧
      M.faces.Finite ∧ G.faces.Finite ∧
      G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ J.space, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ x ∈ M.space) ∧
      IsOpen W ∧ Z ⊆ W ∧
      (∀ a ∈ K.faces, a.card ≤ 2 → g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      EqOn Phi id W ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (Phi '' S i) K g a) ∧
      (Pairwise fun i j => Disjoint (Phi '' S i) (Phi '' S j)) ∧
      (∀ v : G.vertices,
        (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      (∀ v : G.vertices,
        (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) ∧
      (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      ((∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
          intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅) →
      ∃ (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
        (n : ℕ) (L : Polygon V3 (n + 3)) (D : Set V3) (i : κ),
        Function.Injective L ∧ L.HasSimplicialEdges ∧
        L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
        IsFinitePLBallPair P2 D (L.boundary ℝ) ∧ IsCompact D ∧
        D ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) ∧
        D ∩ G.space = L.boundary ℝ ∧
        IsCompact (Q.symm '' D) ∧
        Q.symm '' D ⊆ g '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
        Disjoint (Q.symm '' D) Z ∧
        Disjoint (Q.symm '' D) (⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
          g '' convexHull ℝ (a : Set E)) ∧
        (Q.symm '' D) ∩ Phi '' (⋃ j, S j) = Q.symm '' L.boundary ℝ ∧
        Q.symm '' L.boundary ℝ ⊆ Phi '' S i ∧
        (∀ j, Q.symm '' L.boundary ℝ ⊆ Phi '' S j → j = i) ∧
        ∀ w ∈ L.boundary ℝ, ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 (P2 × ℝ),
            w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source,
              x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0) := by
  classical
  obtain ⟨J, P, P₀, H, M, G, Phi, W, hJ, hJcv, htriJ, hJQ, hP, hPs, hP₀, hP₀sub,
      hM, hMs, hMJ, hMdim, hMpos, hG, hGs, hdim, hphysical, hPhiQ, hPhiout,
      hPhiPL, hPhiinv, hPhiS, hW, hZW, hedgeW, hfixW, hagree, hcofaces', hdisjoint',
      hinterior, hcrossings, hexterior, hfinite, hneigh, hmembers, hwhole,
      hdiscomponents, hcomponents⟩ :=
    exists_original_sphere_system_face_graph_components_with_crossings S sS hdisjoint he K hK g hgc hgi
      hSV hs hs3 hedges hcofaces Q hQ A hmap hA hZ hSZ hε
  have hin (v : G.vertices) :
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := hinterior v v.property
  refine ⟨J, M, G, Phi, W, hJ, hJQ, htriJ, hM, hG, hGs, hdim,
    hPhiPL, hPhiinv, hPhiS, hW, hZW, hedgeW, hfixW, hcofaces', hdisjoint',
    hin, hexterior, hfinite, ?_⟩
  intro hcircle
  have hGne : G.space.Nonempty := by
    obtain ⟨C, hC⟩ := hcircle
    rcases hcomponents C with ⟨n, labels, _, _, hrim, _⟩ | ⟨n, L, _, _, hLC, _⟩
    · have hx : ((labels 0).val : V3) ∈
          C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) :=
        hrim.symm.subset (by simp)
      exact (Set.notMem_empty _ (hC ▸ hx)).elim
    · refine ⟨L 0, ?_⟩
      rw [hwhole]
      exact mem_iUnion.mpr ⟨C, hLC.subset (L.vertex_mem_boundary 0)⟩
  have hsN : s ∉ N.faces := by
    intro hsN
    obtain ⟨x, hxG⟩ := hGne
    have hx := hphysical.subset (mem_image_of_mem Q.symm hxG)
    obtain ⟨u, hu, hux⟩ := hx.2
    have hxZ : Q.symm x ∈ Z := hux ▸
      (hmark u (K.convexHull_subset_space hs hu)).mpr (N.convexHull_subset_space hsN hu)
    obtain ⟨y, hy, hyx⟩ := hx.1
    have hfix : Phi (Q.symm x) = Q.symm x := hfixW (hZW hxZ)
    have hyx' : y = Q.symm x := Phi.injective (hyx.trans hfix.symm)
    exact disjoint_left.mp hSZ hy (hyx'.symm ▸ hxZ)
  obtain ⟨C, n, L, D, i, hLi, hL, hLC, hball, hcompact, hDT, hexact,
      hphysicalcompact, hphysub, hDZ, hDsk, hcapS, hiS, hiunique⟩ :=
    exists_original_face_circle_cap K N hNK g hgi hmark hs hs3 hsN Q A hmap hA
      J M G (htriJ.trans interior_subset) hJQ hG hGs hdim hfinite hin hexterior
      S Phi hPhiS hmembers hcircle
  refine ⟨C, n, L, D, i, hLi, hL, hLC, hball, hcompact, hDT, hexact,
    hphysicalcompact, hphysub, hDZ, hDsk, hcapS, hiS, hiunique, ?_⟩
  intro w hw O hO hwO
  have hwG := (hexact.symm.subset hw).2
  exact hcrossings w ⟨(hGs.subset hwG).1, hDT (hball.1 hw)⟩ O hO hwO

end PoincareConjecture.M76
