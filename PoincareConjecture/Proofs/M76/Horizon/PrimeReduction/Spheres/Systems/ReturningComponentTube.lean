import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.FaceGraphComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.TriangleBoundaryCrossing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.ComponentCrossingFamilies
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.AffineFaceCarrier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.EndpointCappedTube
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.TubeTriangleFrontier

set_option autoImplicit false
open Set Geometry Module

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_original_sphere_system_component_tubes_with_other_faces
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
      (J.faces.Finite ∧ Convex ℝ J.space ∧
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
        P.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))))) ∧
    ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      let d := C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
      ∀ p : Fin 2 → V3, p 0 ≠ p 1 →
        IsFinitePLBallPair ℝ d {p 0, p 1} →
        d ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = {p 0, p 1} →
        ∀ O : Set V3, IsOpen O → d ⊆ O →
          ∃ (R : Set V3) (B : Fin 2 → OpenPartialHomeomorph V3 V3)
            (V : Fin 2 → Set V3) (T : Set V3) (b : I ≃ₜ d)
            (tube : ↥(Dehn.signedTubeDiamond ×ˢ I) ≃ₜ T),
            IsClosed R ∧ d ⊆ R ∧ d ∩ frontier R = {p 0, p 1} ∧
            d \ {p 0, p 1} ⊆ interior R ∧
            (∀ i, B i ∈ piecewiseAffineGroupoid V3 ∧ p i ∈ (B i).source ∧
              (B i).source ⊆ O ∩ interior J.space ∧ B i (p i) = 0) ∧
            Pairwise (fun i j => Disjoint (B i).source (B j).source) ∧
            (∀ i x, x ∈ (B i).source →
              (x ∈ convexHull ℝ (A '' (s : Set E)) ↔ B i x 0 = 0 ∧ 0 ≤ B i x 2)) ∧
            (∀ i x, x ∈ (B i).source → (x ∈ M.space ↔ B i x 1 = 0)) ∧
            (∀ i, IsOpen (V i) ∧ p i ∈ V i ∧ V i ⊆ (B i).source ∩ (O ∩ interior J.space) ∧
              (∀ x ∈ V i, x ∈ R ↔ 0 ≤ B i x 2) ∧
              (∀ x ∈ V i, x ∈ frontier R ↔ B i x 2 = 0)) ∧
            T ⊆ R ∩ (O ∩ interior J.space) ∧ T ⊆ (⋃ i, V i) ∪ interior R ∧
            b.IsFinitePL ∧ (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : V3) = p 0 ∧
            (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : V3) = p 1 ∧ tube.IsFinitePL ∧
            (∀ t : I, (tube ⟨((0, 0), t), Dehn.signedTubeRadius_subset_diamond 0 false
              (left_mem_segment ℝ _ _), t.property⟩ : V3) = b t) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (x : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 0 ↔
                (tube x : V3) ∈ convexHull ℝ (A '' (s : Set E))) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (x : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 1 ↔ (tube x : V3) ∈ M.space) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (tube x : V3) ∈ frontier R ↔ (x : P2 × ℝ).2 = 0 ∨ (x : P2 × ℝ).2 = 1) ∧
            (∃ i, Q.symm '' d ⊆ Phi '' S i ∧
              ∀ j, j ≠ i → Disjoint (Q.symm '' T) (Phi '' S j)) := by
  classical
  obtain ⟨J, P, P₀, H, M, G, Phi, W, hbase⟩ :=
    exists_original_sphere_system_face_graph_components_with_crossings_with_other_faces
      S sS hdisjoint he K hK g hgc hgi hSV hs hs3 hedges hcofaces Q hQ A hmap hA hD hSD hε
  have hcopy := hbase
  obtain ⟨hJ, hcv, htriangleJ, hJQ, hP, hPs, hP₀, hP₀P, hM, hMs, hMJ, hMc,
    hpos, hG, hGs, hGc, hphysical, hPhiQ, hPhiout, hPhiPL, hPhiinv, hPhiS,
    hW, hDW, hfacesW, hPhiW, hagree, hcofaces', hdisjoint', hdegree,
    hcrossings, hboundary, hfinite, hneigh, hmembers, hcomponents⟩ := hcopy
  have heW (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card ≤ 2) :
      g '' convexHull ℝ (a : Set E) ⊆ W :=
    hfacesW a ha (by omega) (by intro h; subst a; omega)
  refine ⟨J, P, P₀, H, M, G, Phi, W, hbase, ?_⟩
  intro C
  dsimp only
  intro p hpne hd hfront O hO hdO
  let d := C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
  have hdG : d ⊆ G.space := fun x hx =>
    hcomponents.1.symm.subset (mem_iUnion.mpr ⟨C, hx⟩)
  have hdJ : d ⊆ interior J.space := fun x hx =>
    htriangleJ (hGs.subset (hdG hx)).2
  obtain ⟨i, hdi, _⟩ := hmembers C
  obtain ⟨N, hN, hSiN, _, hNother⟩ :=
    exists_open_sphere_system_isolation S sS hdisjoint i
  let Ni : Set V3 := Q.target ∩ Q.symm ⁻¹' (Phi.symm ⁻¹' N)
  have hNi : IsOpen Ni := Q.symm.isOpen_inter_preimage
    (hN.preimage Phi.symm.continuous)
  have hdNi : d ⊆ Ni := by
    intro x hx
    refine ⟨hJQ (interior_subset (hdJ hx)), ?_⟩
    obtain ⟨y, hy, hyeq⟩ := hdi ⟨x, hx, rfl⟩
    change Phi.symm (Q.symm x) ∈ N
    rw [← hyeq, Phi.symm_apply_apply]
    exact hSiN hy
  have hNiother (j : κ) (hji : j ≠ i) :
      Disjoint (Q.symm '' Ni) (Phi '' S j) := by
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
    have hn : Phi.symm (Q.symm x) ∈ N := hx.2
    rw [← hzx, Phi.symm_apply_apply] at hn
    exact Set.disjoint_left.mp (hNother j hji) hn hz
  obtain ⟨F, hF, hFs⟩ := K.exists_finite_affine_face_carrier hs A
  have hcopy := hd
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Ar, hAr, hArs, _⟩, _⟩, _⟩ := hcopy
  let marks : Fin 3 → SimplicialComplex ℝ V3 := ![F, M, Ar]
  have hmarks (i : Fin 3) : (marks i).faces.Finite := by
    fin_cases i
    · exact hF
    · exact hM
    · exact hAr
  let sheets : Fin 2 → SimplicialComplex ℝ V3 := fun i => marks i.castSucc
  have hsheets : G.space = (sheets 1).space ∩ (sheets 0).space := by
    simpa [sheets, marks, hFs] using hGs
  have hfront' : d ∩ intrinsicFrontier ℝ (sheets 0).space = {p 0, p 1} := by
    simpa [sheets, marks, hFs] using hfront
  obtain ⟨U, B, Cq, hU, hdU, hUW, hisolate, hB, hpB, hBU, hBp,
      hBtriangle, hBsphere, hCq, hqCq, hCqU, hCqq, hcross⟩ :=
    exists_actual_component_crossing_families sheets G hG hGc hneigh hsheets C p hd
      hfront' ((hO.inter isOpen_interior).inter hNi)
      (fun x hx => ⟨⟨hdO hx, hdJ hx⟩, hdNi hx⟩)
      (by
        intro w hw V hV hwV
        have hw' : w ∈ M.space ∩
            intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) :=
          ⟨(hGs.subset hw.1).1, by simpa [sheets, marks, hFs] using hw.2⟩
        simpa [sheets, marks, hFs] using hcrossings w hw' V hV hwV)
      (by
        intro w hw V hV hwV
        have hw' : w ∈ G.space ∩
            intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) := by
          simpa [sheets, marks, hFs] using hw
        obtain ⟨B, hB, hwB, hBV, hBw, hBM, hBT, _⟩ :=
          exists_original_sphere_system_triangle_boundary_crossing
            S sS hdisjoint K g hgi hSV hs hs3
            (fun i a ha _ ha2 => hcofaces i a ha ha2)
            Q hQ A hmap hA J M G htriangleJ hJQ hGs Phi hPhiS hW
            (fun a ha _ ha2 => heW a ha ha2.le) hagree hw' hV hwV
        refine ⟨B, hB, hwB, (fun x hx => (hBV hx).1), hBw, ?_, ?_⟩
        · simpa [sheets, marks] using hBM
        · simpa [sheets, marks, hFs] using hBT)
  obtain ⟨R, Bcap, Vcap, T, b, tube, hR, hdR, hdfront, hdint,
      hBcap, hdis, hcaptriangle, hcapsphere, hVcap, hTU, hTcover,
      hb, hb0, hb1, htube, haxis, hsheet, hfrontier⟩ :=
    exists_endpoint_capped_tube marks hmarks d p hArs hd hpne U hU hdU
      hisolate B hB hpB hBp hBtriangle hBsphere Cq hCq hqCq hcross
  refine ⟨R, Bcap, Vcap, T, b, tube, hR, hdR, hdfront, hdint, ?_, hdis,
    ?_, ?_, ?_, (fun x hx => ⟨(hTU hx).1, (hUW (hTU hx).2).1⟩),
    hTcover, hb, hb0, hb1, htube, haxis, ?_, ?_, hfrontier, ?_⟩
  · intro i
    exact ⟨(hBcap i).1, (hBcap i).2.1,
      fun x hx => (hUW ((hBcap i).2.2.1 hx)).1, (hBcap i).2.2.2⟩
  · simpa [marks, hFs] using hcaptriangle
  · simpa [marks] using hcapsphere
  · intro i
    obtain ⟨hi, hpi, hVi, hRi, hFi⟩ := hVcap i
    exact ⟨hi, hpi, fun x hx => ⟨(hVi hx).1, (hUW (hVi hx).2).1⟩, hRi, hFi⟩
  · simpa [marks, hFs] using hsheet 0
  · simpa [marks] using hsheet 1

  · refine ⟨i, hdi, ?_⟩
    intro j hji
    exact (hNiother j hji).mono_left (Set.image_mono
      (fun x hx => (hUW (hTU hx).2).2))

theorem exists_original_sphere_system_component_tubes
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
      (J.faces.Finite ∧ Convex ℝ J.space ∧
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
        P.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))))) ∧
    ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      let d := C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
      ∀ p : Fin 2 → V3, p 0 ≠ p 1 →
        IsFinitePLBallPair ℝ d {p 0, p 1} →
        d ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = {p 0, p 1} →
        ∀ O : Set V3, IsOpen O → d ⊆ O →
          ∃ (R : Set V3) (B : Fin 2 → OpenPartialHomeomorph V3 V3)
            (V : Fin 2 → Set V3) (T : Set V3) (b : I ≃ₜ d)
            (tube : ↥(Dehn.signedTubeDiamond ×ˢ I) ≃ₜ T),
            IsClosed R ∧ d ⊆ R ∧ d ∩ frontier R = {p 0, p 1} ∧
            d \ {p 0, p 1} ⊆ interior R ∧
            (∀ i, B i ∈ piecewiseAffineGroupoid V3 ∧ p i ∈ (B i).source ∧
              (B i).source ⊆ O ∩ interior J.space ∧ B i (p i) = 0) ∧
            Pairwise (fun i j => Disjoint (B i).source (B j).source) ∧
            (∀ i x, x ∈ (B i).source →
              (x ∈ convexHull ℝ (A '' (s : Set E)) ↔ B i x 0 = 0 ∧ 0 ≤ B i x 2)) ∧
            (∀ i x, x ∈ (B i).source → (x ∈ M.space ↔ B i x 1 = 0)) ∧
            (∀ i, IsOpen (V i) ∧ p i ∈ V i ∧ V i ⊆ (B i).source ∩ (O ∩ interior J.space) ∧
              (∀ x ∈ V i, x ∈ R ↔ 0 ≤ B i x 2) ∧
              (∀ x ∈ V i, x ∈ frontier R ↔ B i x 2 = 0)) ∧
            T ⊆ R ∩ (O ∩ interior J.space) ∧ T ⊆ (⋃ i, V i) ∪ interior R ∧
            b.IsFinitePL ∧ (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : V3) = p 0 ∧
            (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : V3) = p 1 ∧ tube.IsFinitePL ∧
            (∀ t : I, (tube ⟨((0, 0), t), Dehn.signedTubeRadius_subset_diamond 0 false
              (left_mem_segment ℝ _ _), t.property⟩ : V3) = b t) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (x : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 0 ↔
                (tube x : V3) ∈ convexHull ℝ (A '' (s : Set E))) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (x : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 1 ↔ (tube x : V3) ∈ M.space) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (tube x : V3) ∈ frontier R ↔ (x : P2 × ℝ).2 = 0 ∨ (x : P2 × ℝ).2 = 1) ∧
            (∃ i, Q.symm '' d ⊆ Phi '' S i ∧
              ∀ j, j ≠ i → Disjoint (Q.symm '' T) (Phi '' S j)) := by
  obtain ⟨J, P, P₀, H, M, G, Phi, W, hbase, htubes⟩ :=
    exists_original_sphere_system_component_tubes_with_other_faces S sS hdisjoint he K hK g hgc hgi hSV hs hs3 hedges hcofaces
      Q hQ A hmap hA hD hSD hε
  obtain ⟨hJ, hcv, htriangleJ, hJQ,
      hP, hPs, hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos, hG, hGs, hGc,
      hphysical, hPhiQ, hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW, hfacesW, hrest⟩ := hbase
  refine ⟨J, P, P₀, H, M, G, Phi, W, ⟨hJ, hcv, htriangleJ, hJQ,
      hP, hPs, hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos, hG, hGs, hGc,
      hphysical, hPhiQ, hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW, ?_, hrest⟩, htubes⟩
  intro a ha ha2
  exact hfacesW a ha (by omega) (by intro h; subst a; omega)

theorem exists_original_sphere_system_returning_component_tubes_with_other_faces
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
      (J.faces.Finite ∧ Convex ℝ J.space ∧
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
        P.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))))) ∧
    ∀ a : Finset E, a ⊆ s → a.card = 2 →
    ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      let d := C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
      ∀ p : Fin 2 → V3, p 0 ≠ p 1 →
        IsFinitePLBallPair ℝ d {p 0, p 1} →
        d ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = {p 0, p 1} →
        (∀ i, p i ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (a : Set E)))) →
        ∀ O : Set V3, IsOpen O → d ⊆ O →
          ∃ (R : Set V3) (B : Fin 2 → OpenPartialHomeomorph V3 V3)
            (V : Fin 2 → Set V3) (T : Set V3) (b : I ≃ₜ d)
            (tube : ↥(Dehn.signedTubeDiamond ×ˢ I) ≃ₜ T),
            IsClosed R ∧ d ⊆ R ∧ d ∩ frontier R = {p 0, p 1} ∧
            d \ {p 0, p 1} ⊆ interior R ∧
            (∀ i, B i ∈ piecewiseAffineGroupoid V3 ∧ p i ∈ (B i).source ∧
              (B i).source ⊆ O ∩ interior J.space ∧ B i (p i) = 0) ∧
            Pairwise (fun i j => Disjoint (B i).source (B j).source) ∧
            (∀ i x, x ∈ (B i).source →
              (x ∈ convexHull ℝ (A '' (s : Set E)) ↔ B i x 0 = 0 ∧ 0 ≤ B i x 2)) ∧
            (∀ i x, x ∈ (B i).source → (x ∈ M.space ↔ B i x 1 = 0)) ∧
            (∀ i, IsOpen (V i) ∧ p i ∈ V i ∧ V i ⊆ (B i).source ∩ (O ∩ interior J.space) ∧
              (∀ x ∈ V i, x ∈ R ↔ 0 ≤ B i x 2) ∧
              (∀ x ∈ V i, x ∈ frontier R ↔ B i x 2 = 0)) ∧
            T ⊆ R ∩ (O ∩ interior J.space) ∧ T ⊆ (⋃ i, V i) ∪ interior R ∧
            b.IsFinitePL ∧ (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : V3) = p 0 ∧
            (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : V3) = p 1 ∧ tube.IsFinitePL ∧
            (∀ t : I, (tube ⟨((0, 0), t), Dehn.signedTubeRadius_subset_diamond 0 false
              (left_mem_segment ℝ _ _), t.property⟩ : V3) = b t) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (x : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 0 ↔
                (tube x : V3) ∈ convexHull ℝ (A '' (s : Set E))) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (x : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 1 ↔ (tube x : V3) ∈ M.space) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (tube x : V3) ∈ frontier R ↔ (x : P2 × ℝ).2 = 0 ∨ (x : P2 × ℝ).2 = 1) ∧
            (∀ z : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (z : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 0 →
              ((z : P2 × ℝ).2 = 0 ∨ (z : P2 × ℝ).2 = 1) →
              (tube z : V3) ∈ convexHull ℝ (A '' (a : Set E))) ∧
            (∀ F : V3 → P2,
              (∀ y ∈ convexHull ℝ (A '' (a : Set E)), (F y).2 = 0) →
              ∀ z : ↥(Dehn.signedTubeDiamond ×ˢ I),
                (z : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 0 →
                ((z : P2 × ℝ).2 = 0 ∨ (z : P2 × ℝ).2 = 1) →
                (F (tube z)).2 = 0) ∧
            (∃ i, Q.symm '' d ⊆ Phi '' S i ∧
              ∀ j, j ≠ i → Disjoint (Q.symm '' T) (Phi '' S j)) := by
  classical
  obtain ⟨J, P, P₀, H, M, G, Phi, W, hbase, htubes⟩ :=
    exists_original_sphere_system_component_tubes_with_other_faces
      S sS hdisjoint he K hK g hgc hgi hSV hs hs3 hedges hcofaces Q hQ A hmap hA hD hSD hε
  refine ⟨J, P, P₀, H, M, G, Phi, W, hbase, ?_⟩
  intro a hat ha2 C
  dsimp only
  intro p hpne hd hfront hpedge O hO hdO
  let t := s.image A
  let c := a.image A
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hgi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      (Q.injOn (hmap hx) (hmap hy) ((hA hx).trans (hxy.trans (hA hy).symm)))
  have hAis : InjOn A (s : Set E) := hAi.mono (subset_convexHull ℝ _)
  have ht : AffineIndependent ℝ ((↑) : t → V3) := by
    change AffineIndependent ℝ ((↑) : ↥(t : Set V3) → V3)
    rw [show (t : Set V3) = A '' (s : Set E) by simp only [t, Finset.coe_image]]
    exact affineIndependent_original_face_chart K g hgi hs Q A hmap hA
  have ht3 : t.card = 3 := (Finset.card_image_iff.mpr hAis).trans hs3
  have hc2 : c.card = 2 := (Finset.card_image_iff.mpr (hAis.mono hat)).trans ha2
  have hct : c ⊆ t := Finset.image_subset_image hat
  have hcontact :
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (t : Set V3)) ⊆
          intrinsicInterior ℝ (convexHull ℝ (c : Set V3)) := by
    intro x hx
    have he : x ∈ ({p 0, p 1} : Set V3) := hfront.subset (by
      simpa only [t, Finset.coe_image] using hx)
    rcases he with rfl | he
    · simpa only [c, Finset.coe_image] using hpedge 0
    · have he' : x = p 1 := he
      simpa only [he', c, Finset.coe_image] using hpedge 1
  obtain ⟨U, hU, hdU, hUbase⟩ :=
    exists_open_returning_triangle_base_neighborhood t c ht ht3 hct hc2 hcontact
  obtain ⟨R, B, V, T, b, tube, hR, hdR, hdF, hdint, hB, hdis, hBT, hBM, hV,
      hT, hcover, hb, hb0, hb1, htube, haxis, hsheet0, hsheet1, hfrontier, hmember⟩ :=
    htubes C p hpne hd hfront (O ∩ U) (hO.inter hU) (fun x hx => ⟨hdO hx, hdU hx⟩)
  have htriangle (i : Fin 2) (y : V3) (hy : y ∈ (B i).source) :
      y ∈ convexHull ℝ (t : Set V3) ↔ B i y 0 = 0 ∧ 0 ≤ B i y 2 := by
    simpa only [t, Finset.coe_image] using hBT i y hy
  have hends (z : ↥(Dehn.signedTubeDiamond ×ˢ I))
      (hzsheet : (z : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 0)
      (hz : (z : P2 × ℝ).2 = 0 ∨ (z : P2 × ℝ).2 = 1) :
      (tube z : V3) ∈ convexHull ℝ (A '' (a : Set E)) := by
    have hf := tube_endface_triangle_mem_intrinsicFrontier t ht ht3 tube B
      (fun i => (hB i).1) htriangle V
      (fun i x hx => ((hV i).2.2.1 hx).1) hcover
      (fun i => (hV i).2.2.2.2) hfrontier z hz
      (by simpa only [t, Finset.coe_image] using (hsheet0 z).mp hzsheet)
    have hu : (tube z : V3) ∈ U := (hT (tube z).property).2.1.2
    simpa only [c, Finset.coe_image] using (hUbase _ hu).mp hf
  refine ⟨R, B, V, T, b, tube, hR, hdR, hdF, hdint, ?_, hdis, hBT, hBM,
    ?_, ?_, hcover, hb, hb0, hb1, htube, haxis, hsheet0, hsheet1, hfrontier,
    hends, ?_, hmember⟩
  · intro i
    exact ⟨(hB i).1, (hB i).2.1,
      fun x hx => ⟨((hB i).2.2.1 hx).1.1, ((hB i).2.2.1 hx).2⟩,
      (hB i).2.2.2⟩
  · intro i
    obtain ⟨hi, hpi, hVi, hRi, hFi⟩ := hV i
    exact ⟨hi, hpi, fun x hx => ⟨(hVi hx).1, (hVi hx).2.1.1, (hVi hx).2.2⟩,
      hRi, hFi⟩
  · exact fun x hx => ⟨(hT hx).1, (hT hx).2.1.1, (hT hx).2.2⟩
  · exact fun F hF z hzsheet hz => hF _ (hends z hzsheet hz)

theorem exists_original_sphere_system_returning_component_tubes
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
      (J.faces.Finite ∧ Convex ℝ J.space ∧
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
        P.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))))) ∧
    ∀ a : Finset E, a ⊆ s → a.card = 2 →
    ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      let d := C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
      ∀ p : Fin 2 → V3, p 0 ≠ p 1 →
        IsFinitePLBallPair ℝ d {p 0, p 1} →
        d ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = {p 0, p 1} →
        (∀ i, p i ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (a : Set E)))) →
        ∀ O : Set V3, IsOpen O → d ⊆ O →
          ∃ (R : Set V3) (B : Fin 2 → OpenPartialHomeomorph V3 V3)
            (V : Fin 2 → Set V3) (T : Set V3) (b : I ≃ₜ d)
            (tube : ↥(Dehn.signedTubeDiamond ×ˢ I) ≃ₜ T),
            IsClosed R ∧ d ⊆ R ∧ d ∩ frontier R = {p 0, p 1} ∧
            d \ {p 0, p 1} ⊆ interior R ∧
            (∀ i, B i ∈ piecewiseAffineGroupoid V3 ∧ p i ∈ (B i).source ∧
              (B i).source ⊆ O ∩ interior J.space ∧ B i (p i) = 0) ∧
            Pairwise (fun i j => Disjoint (B i).source (B j).source) ∧
            (∀ i x, x ∈ (B i).source →
              (x ∈ convexHull ℝ (A '' (s : Set E)) ↔ B i x 0 = 0 ∧ 0 ≤ B i x 2)) ∧
            (∀ i x, x ∈ (B i).source → (x ∈ M.space ↔ B i x 1 = 0)) ∧
            (∀ i, IsOpen (V i) ∧ p i ∈ V i ∧ V i ⊆ (B i).source ∩ (O ∩ interior J.space) ∧
              (∀ x ∈ V i, x ∈ R ↔ 0 ≤ B i x 2) ∧
              (∀ x ∈ V i, x ∈ frontier R ↔ B i x 2 = 0)) ∧
            T ⊆ R ∩ (O ∩ interior J.space) ∧ T ⊆ (⋃ i, V i) ∪ interior R ∧
            b.IsFinitePL ∧ (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : V3) = p 0 ∧
            (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : V3) = p 1 ∧ tube.IsFinitePL ∧
            (∀ t : I, (tube ⟨((0, 0), t), Dehn.signedTubeRadius_subset_diamond 0 false
              (left_mem_segment ℝ _ _), t.property⟩ : V3) = b t) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (x : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 0 ↔
                (tube x : V3) ∈ convexHull ℝ (A '' (s : Set E))) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (x : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 1 ↔ (tube x : V3) ∈ M.space) ∧
            (∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (tube x : V3) ∈ frontier R ↔ (x : P2 × ℝ).2 = 0 ∨ (x : P2 × ℝ).2 = 1) ∧
            (∀ z : ↥(Dehn.signedTubeDiamond ×ˢ I),
              (z : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 0 →
              ((z : P2 × ℝ).2 = 0 ∨ (z : P2 × ℝ).2 = 1) →
              (tube z : V3) ∈ convexHull ℝ (A '' (a : Set E))) ∧
            (∀ F : V3 → P2,
              (∀ y ∈ convexHull ℝ (A '' (a : Set E)), (F y).2 = 0) →
              ∀ z : ↥(Dehn.signedTubeDiamond ×ˢ I),
                (z : P2 × ℝ).1 ∈ Dehn.signedTubeSheet 0 →
                ((z : P2 × ℝ).2 = 0 ∨ (z : P2 × ℝ).2 = 1) →
                (F (tube z)).2 = 0) ∧
            (∃ i, Q.symm '' d ⊆ Phi '' S i ∧
              ∀ j, j ≠ i → Disjoint (Q.symm '' T) (Phi '' S j)) := by
  obtain ⟨J, P, P₀, H, M, G, Phi, W, hbase, htubes⟩ :=
    exists_original_sphere_system_returning_component_tubes_with_other_faces S sS hdisjoint he K hK g hgc hgi hSV hs hs3 hedges hcofaces
      Q hQ A hmap hA hD hSD hε
  obtain ⟨hJ, hcv, htriangleJ, hJQ,
      hP, hPs, hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos, hG, hGs, hGc,
      hphysical, hPhiQ, hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW, hfacesW, hrest⟩ := hbase
  refine ⟨J, P, P₀, H, M, G, Phi, W, ⟨hJ, hcv, htriangleJ, hJQ,
      hP, hPs, hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos, hG, hGs, hGc,
      hphysical, hPhiQ, hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW, ?_, hrest⟩, htubes⟩
  intro a ha ha2
  exact hfacesW a ha (by omega) (by intro h; subst a; omega)

end PoincareConjecture.M76
