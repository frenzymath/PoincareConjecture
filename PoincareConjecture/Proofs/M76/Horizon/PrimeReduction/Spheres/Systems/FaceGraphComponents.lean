import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SkeletonFaceGraphMotion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ComponentMembership
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalTriangleBoundaryDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.AffineTriangleComponents









set_option autoImplicit false
open Set Geometry Module Filter
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ncard_sphere_system_triangle_boundary_neighborSet_eq_one
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (K : SimplicialComplex ℝ E) (g : E → X)
    (hgi : InjOn g K.space) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGQ : G.space ⊆ Q.target)
    (hGt : G.space ⊆ convexHull ℝ (A '' (s : Set E)))
    (Phi : X ≃ₜ X) {W : Set X} (hW : IsOpen W)
    (hedgeW : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      g '' convexHull ℝ (a : Set E) ⊆ W)
    (hagree : Phi '' (⋃ i, S i) ∩ W = (⋃ i, S i) ∩ W)
    (hphysical : Q.symm '' G.space = Phi '' (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E))) :
    ∀ w : G.vertices,
      (w : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet w).ncard = 1 := by
  classical
  have himage : A '' convexHull ℝ (s : Set E) = convexHull ℝ (A '' (s : Set E)) :=
    A.toAffineMap.image_convexHull _
  intro w hw
  have hwG : (w : V3) ∈ G.space := G.vertices_subset_space w.property
  have hwQ : (w : V3) ∈ Q.target := hGQ hwG
  have hwfront : (w : V3) ∈ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) := by
    rw [← closure_sdiff_intrinsicInterior]
    exact ⟨subset_closure (hGt hwG), hw⟩
  obtain ⟨a, ha, has, ha2, _, _, hyedge⟩ :=
    exists_original_subedge_of_mem_triangle_intrinsicFrontier K g hgi hs hs3 Q A hmap hA hwfront
  have hyW : Q.symm w ∈ W := hedgeW a ha has ha2 hyedge
  have hyPhi : Q.symm w ∈ Phi '' (⋃ i, S i) := (hphysical.subset ⟨w, hwG, rfl⟩).1
  have hyS : Q.symm w ∈ ⋃ i, S i := (hagree.subset ⟨hyPhi, hyW⟩).1
  have hlocal : ∀ᶠ x in 𝓝 (w : V3), x ∈ G.space ↔
      x ∈ Q '' ((⋃ i, S i) ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E)) := by
    have hU : IsOpen (Q.target ∩ Q.symm ⁻¹' W) := Q.symm.isOpen_inter_preimage hW
    filter_upwards [hU.mem_nhds ⟨hwQ, hyW⟩] with x hxU
    constructor
    · intro hxG
      have hxPhi : Q.symm x ∈ Phi '' (⋃ i, S i) := (hphysical.subset ⟨x, hxG, rfl⟩).1
      have hxS : Q.symm x ∈ ⋃ i, S i := (hagree.subset ⟨hxPhi, hxU.2⟩).1
      exact ⟨⟨Q.symm x, ⟨hxS, Q.map_target hxU.1⟩, Q.right_inv hxU.1⟩, hGt hxG⟩
    · rintro ⟨⟨y, ⟨hyS, hyQ⟩, hyx⟩, hxt⟩
      have hxS : Q.symm x ∈ ⋃ i, S i := by rw [← hyx, Q.left_inv hyQ]; exact hyS
      have hxPhi : Q.symm x ∈ Phi '' (⋃ i, S i) := (hagree.symm.subset ⟨hxS, hxU.2⟩).1
      obtain ⟨v, hv, hvx⟩ := himage.symm.subset hxt
      have hQgv : Q (g v) = x := (hA hv).trans hvx
      have hgv : g v = Q.symm x := (Q.left_inv (hmap hv)).symm.trans (congrArg Q.symm hQgv)
      obtain ⟨z, hzG, hzx⟩ := hphysical.symm.subset ⟨hxPhi, v, hv, hgv⟩
      exact Q.symm.injOn (hGQ hzG) hxU.1 hzx ▸ hzG
  have hmarked : Q (Q.symm w) ∈ G.vertices := by rw [Q.right_inv hwQ]; exact w.property
  obtain ⟨i, hyi⟩ := mem_iUnion.mp hyS
  obtain ⟨O, hO, hwO, _, hOi⟩ := exists_sphere_system_chart_isolation
    S sS hdis Q i hyi (Q.map_target hwQ)
  have hwO' : (w : V3) ∈ O := by simpa only [Q.right_inv hwQ] using hwO
  have hmember : ∀ᶠ x in 𝓝 (w : V3), x ∈ G.space ↔
      x ∈ Q '' (S i ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E)) := by
    filter_upwards [hlocal, hO.mem_nhds hwO'] with x hx hxO
    exact hx.trans (and_congr_left (fun _ => hOi x hxO))
  have hdegree := (hcofaces i a ha has ha2).ncard_contact_neighborSet_eq_one_of_affine_chart
      (sS i) hs hs3 has ha2 hgi (hSV.mono_left (subset_iUnion S i))
      ⟨hyi, hyedge⟩ Q hQ A hmap hA G hG hmarked
      (by simpa only [Q.right_inv hwQ] using hmember)
  simpa only [Q.right_inv hwQ] using hdegree




theorem exists_original_sphere_system_face_graph_components_with_crossings_with_other_faces
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgc : ContinuousOn g K.space)
    (hgi : InjOn g K.space) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 →
      HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {D : Set X} (hD : IsClosed D) (hSD : Disjoint (⋃ i, S i) D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (J P P₀ : SimplicialComplex ℝ V3)
      (H : PLCarrierMotion J.space P₀.space ε)
      (M G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) (W : Set X),
      J.faces.Finite ∧ Convex ℝ J.space ∧
      convexHull ℝ (A '' (s : Set E)) ⊆ interior J.space ∧ J.space ⊆ Q.target ∧
      P.faces.Finite ∧ P.space = Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space ∧
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧
      M.faces.Finite ∧ M.space = H.map 1 '' P.space ∧ M.space ⊆ J.space ∧
      (∀ a ∈ M.faces, a.card ≤ 3) ∧
      (∀ a ∈ M.faces,
        convexHull ℝ (a : Set V3) ⊆ P₀.space ∨
          affineSpan ℝ ((a : Set V3) ∪ A '' (s : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
              (convexHull ℝ (A '' (s : Set E)))) ∧
      G.faces.Finite ∧ G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      Q.symm '' G.space = Phi '' (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (∀ x ∈ Q.target, Phi (Q.symm x) = Q.symm (H.map 1 x)) ∧
      EqOn Phi id (Q.symm '' J.space)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ J.space, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ x ∈ M.space) ∧
      IsOpen W ∧ D ⊆ W ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      EqOn Phi id W ∧ Phi '' (⋃ i, S i) ∩ W = (⋃ i, S i) ∩ W ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (Phi '' S i) K g a) ∧
      (Pairwise fun i j => Disjoint (Phi '' S i) (Phi '' S j)) ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) ∧
      (∀ w ∈ M.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
        ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 ((ℝ × ℝ) × ℝ),
            w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source,
              x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0) ∧
      (∀ w : G.vertices,
        (w : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet w).ncard = 1) ∧
      (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      (∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty) ∧
      (∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        ∃! i, Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ Phi '' S i) ∧
    G.space = ⋃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
    Pairwise (fun C D : G.vertexAbstractComplex.edgeGraph.ConnectedComponent =>
      Disjoint (C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))
        (D.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))) ∧
    ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∃ (n : ℕ) (e : Fin (n + 2) ≃ C),
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) =
          Polygon.pathCarrier (fun i => ((e i).val : V3)) ∧
        IsFinitePLBallPair ℝ (C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))
          (C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))) ∧
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) =
          {((e 0).val : V3), ((e (Fin.last (n + 1))).val : V3)} ∧
        ∀ v w : C, C.toSimpleGraph.Adj v w ↔ ∃ i : Fin (n + 1),
          (e i.castSucc = v ∧ e i.succ = w) ∨
          (e i.castSucc = w ∧ e i.succ = v)) ∨
      (∃ (n : ℕ) (P : Polygon V3 (n + 3)), Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
        P.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))) := by
  classical
  obtain ⟨J, P, P₀, H, M, G, Phi, W, hJ, hcv, htriangleJ, hJQ,
      hP, hPs, hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos, hG, hGs, hGc,
      hphysical, hPhiQ, hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW,
      hfacesW, hPhiW, hagree, hcofaces', hdisjoint', hdegree, hcrossings⟩ :=
    exists_original_sphere_system_other_faces_graph_motion_with_crossings
      S sS hdisjoint he K hK g hgc hgi hSV hs hs3 hedges hcofaces
      Q hQ A hmap hA hD hSD hε
  have heW (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card ≤ 2) :
      g '' convexHull ℝ (a : Set E) ⊆ W :=
    hfacesW a ha (by omega) (by intro h; subst a; omega)
  have hGt : G.space ⊆ convexHull ℝ (A '' (s : Set E)) :=
    fun x hx => (hGs.subset hx).2
  have hGQ : G.space ⊆ Q.target :=
    fun x hx => hJQ (hMJ (hGs.subset hx).1)
  have heW' : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      g '' convexHull ℝ (a : Set E) ⊆ W :=
    fun a ha _ ha2 => heW a ha ha2.le
  have hboundary := ncard_sphere_system_triangle_boundary_neighborSet_eq_one
    S sS hdisjoint K g hgi hSV hs hs3
      (fun i a ha _ ha2 => hcofaces i a ha ha2) Q hQ A hmap hA
      G hG hGQ hGt Phi hW heW' hagree hphysical
  have hfinite := finite_original_triangle_graph_boundary K g hgi hs hs3 (⋃ i, S i)
    (fun a ha _ ha2 => hedges a ha ha2) Q A hmap hA G Phi heW' hagree hphysical
  have hne (v : G.vertices) : (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    by_cases hv : (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))
    · rw [hdegree v v.property hv]
      norm_num
    · rw [hboundary v hv]
      norm_num
  have hmembers (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      ∃! i, Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ Phi '' S i :=
    exists_unique_moved_sphere_member_of_graph_component S sS hdisjoint Phi Q G hGQ
      (hphysical.subset.trans inter_subset_left) hne C
  have hcomponents := exists_original_triangle_graph_components K g hgi hs hs3
    Q A hmap hA G hG hGc hGt hfinite (fun v hv => hdegree v v.property hv) hboundary
  exact ⟨J, P, P₀, H, M, G, Phi, W, hJ, hcv, htriangleJ, hJQ,
    hP, hPs, hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos, hG, hGs, hGc,
    hphysical, hPhiQ, hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW,
    hfacesW, hPhiW, hagree, hcofaces', hdisjoint', hdegree, hcrossings,
    hboundary, hfinite, hne, hmembers, hcomponents⟩


theorem exists_original_sphere_system_face_graph_components_with_crossings
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgc : ContinuousOn g K.space)
    (hgi : InjOn g K.space) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 →
      HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {D : Set X} (hD : IsClosed D) (hSD : Disjoint (⋃ i, S i) D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (J P P₀ : SimplicialComplex ℝ V3)
      (H : PLCarrierMotion J.space P₀.space ε)
      (M G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) (W : Set X),
      J.faces.Finite ∧ Convex ℝ J.space ∧
      convexHull ℝ (A '' (s : Set E)) ⊆ interior J.space ∧ J.space ⊆ Q.target ∧
      P.faces.Finite ∧ P.space = Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space ∧
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧
      M.faces.Finite ∧ M.space = H.map 1 '' P.space ∧ M.space ⊆ J.space ∧
      (∀ a ∈ M.faces, a.card ≤ 3) ∧
      (∀ a ∈ M.faces,
        convexHull ℝ (a : Set V3) ⊆ P₀.space ∨
          affineSpan ℝ ((a : Set V3) ∪ A '' (s : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
              (convexHull ℝ (A '' (s : Set E)))) ∧
      G.faces.Finite ∧ G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      Q.symm '' G.space = Phi '' (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (∀ x ∈ Q.target, Phi (Q.symm x) = Q.symm (H.map 1 x)) ∧
      EqOn Phi id (Q.symm '' J.space)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ J.space, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ x ∈ M.space) ∧
      IsOpen W ∧ D ⊆ W ∧
      (∀ a ∈ K.faces, a.card ≤ 2 →
        g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      EqOn Phi id W ∧ Phi '' (⋃ i, S i) ∩ W = (⋃ i, S i) ∩ W ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (Phi '' S i) K g a) ∧
      (Pairwise fun i j => Disjoint (Phi '' S i) (Phi '' S j)) ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) ∧
      (∀ w ∈ M.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
        ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 ((ℝ × ℝ) × ℝ),
            w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source,
              x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0) ∧
      (∀ w : G.vertices,
        (w : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet w).ncard = 1) ∧
      (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      (∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty) ∧
      (∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        ∃! i, Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ Phi '' S i) ∧
    G.space = ⋃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
    Pairwise (fun C D : G.vertexAbstractComplex.edgeGraph.ConnectedComponent =>
      Disjoint (C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))
        (D.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))) ∧
    ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∃ (n : ℕ) (e : Fin (n + 2) ≃ C),
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) =
          Polygon.pathCarrier (fun i => ((e i).val : V3)) ∧
        IsFinitePLBallPair ℝ (C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))
          (C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))) ∧
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) =
          {((e 0).val : V3), ((e (Fin.last (n + 1))).val : V3)} ∧
        ∀ v w : C, C.toSimpleGraph.Adj v w ↔ ∃ i : Fin (n + 1),
          (e i.castSucc = v ∧ e i.succ = w) ∨
          (e i.castSucc = w ∧ e i.succ = v)) ∨
      (∃ (n : ℕ) (P : Polygon V3 (n + 3)), Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
        P.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))) := by
  obtain ⟨J, P, P₀, H, M, G, Phi, W, hJ, hcv, htriangleJ, hJQ,
      hP, hPs, hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos, hG, hGs, hGc,
      hphysical, hPhiQ, hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW, hfacesW, hrest⟩ :=
    exists_original_sphere_system_face_graph_components_with_crossings_with_other_faces S sS hdisjoint he K hK g hgc hgi hSV hs hs3 hedges hcofaces
      Q hQ A hmap hA hD hSD hε
  refine ⟨J, P, P₀, H, M, G, Phi, W, hJ, hcv, htriangleJ, hJQ,
      hP, hPs, hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos, hG, hGs, hGc,
      hphysical, hPhiQ, hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW, ?_, hrest⟩
  intro a ha ha2
  exact hfacesW a ha (by omega) (by intro h; subst a; omega)

end PoincareConjecture.M76
