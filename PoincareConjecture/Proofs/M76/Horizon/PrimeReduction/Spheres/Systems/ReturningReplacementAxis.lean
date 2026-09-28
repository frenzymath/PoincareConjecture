import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ReturningComponentTube
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalTriangleReturningBigons
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.OuterTubeStrand
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.InnermostReturningContacts

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.OuterStrandContacts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.ProjectedFaceContacts










set_option autoImplicit false
open Set Geometry Module TriangleDiskModel

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

private theorem right_triangle_axis_mem_base {z : P2}
    (hz : z ∈ convexHull ℝ (range rightTriangle)) (hzero : z.2 = 0) :
    z ∈ segment ℝ (0, 0) (1, 0) := by
  rw [Polygon.returning_axis_segment rfl rfl (by norm_num : (0 : ℝ) ≤ 1)]
  obtain ⟨h0, _, h1⟩ := (mem_right_region_iff z).mp hz
  exact ⟨⟨h0, by simpa only [hzero, add_zero] using h1⟩, hzero⟩

private theorem right_triangle_axis_mem_frontier {z : P2}
    (hz : z ∈ convexHull ℝ (range rightTriangle)) (hzero : z.2 = 0) :
    z ∈ frontier (convexHull ℝ (range rightTriangle)) := by
  rw [rightTriangle.frontier_convexHull_triangle independent_rightTriangle]
  apply mem_iUnion.mpr
  refine ⟨(0 : Fin 3), ?_⟩
  simpa [Polygon.edgeSet, Polygon.edgeVertices, rightTriangle, affineSegment_eq_segment]
    using right_triangle_axis_mem_base hz hzero

private theorem edge_hull_mem_intrinsicInterior_of_not_vertex
    (a : Finset V3) (ha : AffineIndependent ℝ ((↑) : a → V3))
    (ha2 : a.card = 2) {x : V3} (hx : x ∈ convexHull ℝ (a : Set V3))
    (hxv : x ∉ a) : x ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V3)) := by
  by_contra hn
  have hfront : x ∈ intrinsicFrontier ℝ (convexHull ℝ (a : Set V3)) := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hx, hn⟩
  obtain ⟨v, hv, hxv'⟩ := (ha.mem_intrinsicFrontier_convexHull_finset
    (Finset.card_pos.mp (by omega)) x).mp hfront
  have hcard : (a.erase v).card = 1 := by rw [Finset.card_erase_of_mem hv, ha2]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
  have hxw : x = w := by simpa only [hw, Finset.coe_singleton, convexHull_singleton,
    mem_singleton_iff] using hxv'
  exact hxv (hxw.symm ▸ Finset.mem_of_mem_erase
    (show w ∈ a.erase v by rw [hw]; simp))

private theorem original_returning_endpoint_mem_base_interior
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (hSV : Disjoint S (g '' K.vertices))
    {s a : Finset E} (hs : s ∈ K.faces) (has : a ⊆ s) (ha2 : a.card = 2)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) {W : Set X}
    (hedgeW : g '' convexHull ℝ (a : Set E) ⊆ W)
    (hagree : Phi '' S ∩ W = S ∩ W)
    (hphysical : Q.symm '' G.space = Phi '' S ∩ (g '' convexHull ℝ (s : Set E)))
    {x : V3} (hxG : x ∈ G.space) (hxa : x ∈ convexHull ℝ (A '' (a : Set E))) :
    x ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (a : Set E))) := by
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hgi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      (Q.injOn (hmap hx) (hmap hy) ((hA hx).trans (hxy.trans (hA hy).symm)))
  have hAis : InjOn A (s : Set E) := hAi.mono (subset_convexHull ℝ _)
  have hind := affineIndependent_original_face_chart K g hgi hs Q A hmap hA
  have hinda : AffineIndependent ℝ ((↑) : (a.image A) → V3) := by
    change AffineIndependent ℝ ((↑) : ↥((a.image A : Finset V3) : Set V3) → V3)
    rw [Finset.coe_image]
    exact hind.mono (image_mono has)
  have hxnot : x ∉ a.image A := by
    rintro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have hvs : v ∈ convexHull ℝ (s : Set E) := subset_convexHull ℝ _ (has hv)
    have hQa : Q.symm (A v) = g v := by
      rw [← hA hvs]
      exact Q.left_inv (hmap hvs)
    have hvPhi : g v ∈ Phi '' S := by
      rw [← hQa]
      exact (hphysical.subset ⟨A v, hxG, rfl⟩).1
    have hvW : g v ∈ W := hedgeW ⟨v, subset_convexHull ℝ _ hv, rfl⟩
    exact disjoint_left.mp hSV (hagree.subset ⟨hvPhi, hvW⟩).1
      ⟨v, K.face_subset_vertices hs (has hv), rfl⟩
  have hcard : (a.image A).card = 2 :=
    (Finset.card_image_iff.mpr (hAis.mono has)).trans ha2
  simpa only [Finset.coe_image] using edge_hull_mem_intrinsicInterior_of_not_vertex
    (a.image A) hinda hcard (by simpa only [Finset.coe_image] using hxa) hxnot

private theorem exists_axis_ordered_endpoints (R : V3 → P2) {x y : V3}
    (hxy : R x ≠ R y) (hx : (R x).2 = 0) (hy : (R y).2 = 0) :
    ∃ p : Fin 2 → V3, ({p 0, p 1} : Set V3) = {x, y} ∧
      p 0 ≠ p 1 ∧ (R (p 0)).1 < (R (p 1)).1 := by
  have hfirst : (R x).1 ≠ (R y).1 := fun h => hxy (Prod.ext h (hx.trans hy.symm))
  rcases lt_or_gt_of_ne hfirst with h | h
  · refine ⟨![x, y], by simp, ?_, h⟩
    exact fun he => hxy (congrArg R he)
  · refine ⟨![y, x], by simp [pair_comm], ?_, h⟩
    exact fun he => hxy (congrArg R he.symm)

private theorem ribbon_end_trace_mem_open_base {r : ℝ} (hr : 0 < r)
    (f : P2 → P2) (hf : FinitePiecewiseAffineOn f (Icc (-r) r ×ˢ I))
    (hi : InjOn f (Icc (-r) r ×ˢ I)) {t : ℝ} (ht : t ∈ I)
    (hbase : ∀ c ∈ Icc (-r) r, f (c, t) ∈ Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ))
    {c : ℝ} (hc : c ∈ Ioo (-r) r) : (f (c, t)).1 ∈ Ioo (0 : ℝ) 1 := by
  have hI := isFinitePLBallPair_Icc (show -r < r by linarith)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI
  let line : ℝ →ᴬ[ℝ] P2 :=
    (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ t)
  have hline : FinitePiecewiseAffineOn line (Icc (-r) r) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine line⟩
  have htrace : FinitePiecewiseAffineOn (fun c => f (c, t)) (Icc (-r) r) :=
    hf.comp hline (fun c hc => ⟨hc, ht⟩)
  have hscalar : FinitePiecewiseAffineOn (fun c => (f (c, t)).1) (Icc (-r) r) := by
    obtain ⟨N, hN, hNs, hNt⟩ := htrace
    exact ⟨N, hN, hNs, hNt.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap⟩
  have hscalarInj : InjOn (fun c => (f (c, t)).1) (Icc (-r) r) := by
    intro c hc d hd heq
    have hp : f (c, t) = f (d, t) :=
      Prod.ext heq ((hbase c hc).2.trans (hbase d hd).2.symm)
    exact congrArg Prod.fst (hi ⟨hc, ht⟩ ⟨hd, ht⟩ hp)
  have hopen := hscalar.mem_interior_image rfl hscalarInj
    (show c ∈ interior (Icc (-r) r) by simpa only [interior_Icc] using hc)
  have hsub : (fun c => (f (c, t)).1) '' Icc (-r) r ⊆ Icc (0 : ℝ) 1 := by
    rintro _ ⟨c, hc, rfl⟩
    exact (hbase c hc).1
  simpa only [interior_Icc] using interior_mono hsub hopen





theorem exists_original_sphere_system_returning_replacement_strands_with_other_faces
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
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {D : Set X} (hD : IsClosed D) (hSD : Disjoint (⋃ i, S i) D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (J M G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) (W : Set X),
      J.faces.Finite ∧ convexHull ℝ (A '' (s : Set E)) ⊆ interior J.space ∧
      J.space ⊆ Q.target ∧ M.faces.Finite ∧ M.space ⊆ J.space ∧ G.faces.Finite ∧
      G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      Q.symm '' G.space = Phi '' (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      EqOn Phi id (Q.symm '' J.space)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ J.space, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ x ∈ M.space) ∧
      IsOpen W ∧ D ⊆ W ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s → g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      EqOn Phi id W ∧ Phi '' (⋃ i, S i) ∩ W = (⋃ i, S i) ∩ W ∧
      (∀ w ∈ M.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
        ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 ((ℝ × ℝ) × ℝ),
            w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source,
              x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0) ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) ∧
      (∀ w : G.vertices,
        (w : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet w).ncard = 1) ∧
      (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      ∀ a : Finset E, a ⊆ s → a.card = 2 →
      (∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
            convexHull ℝ (A '' (a : Set E))) →
      let Iret := {C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent //
        (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
            convexHull ℝ (A '' (a : Set E))}
      ∃ (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
        (n : Iret → ℕ) (labels : ∀ j, Fin (n j + 2) ≃ j.val)
        (polys : ∀ j, Polygon P2 (n j + 3)) (i : Iret) (p : Fin 2 → V3),
        let d := i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
        Function.LeftInverse R F ∧ EqOn (F ∘ R) id (affineSpan ℝ (A '' (s : Set E))) ∧
        F '' convexHull ℝ (range rightTriangle) = convexHull ℝ (A '' (s : Set E)) ∧
        F '' segment ℝ (0, 0) (1, 0) = convexHull ℝ (A '' (a : Set E)) ∧
        (∀ j, (polys j).HasSimplicialEdges ∧ Function.Injective (polys j)) ∧
        (∀ j k, 0 ≤ (polys j k).2) ∧
        (∀ j, (polys j).boundary ℝ =
          R '' j.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∪
          segment ℝ (R ((labels j 0).val : V3))
            (R ((labels j (Fin.last (n j + 1))).val : V3))) ∧
        closure (polys i).inside ∩ (⋃ j, (polys j).boundary ℝ) = (polys i).boundary ℝ ∧
        Disjoint (polys i).inside (⋃ j, (polys j).boundary ℝ) ∧
        IsFinitePLBallPair P2 (closure (polys i).inside) ((polys i).boundary ℝ) ∧
        closure (polys i).inside ⊆ convexHull ℝ (range rightTriangle) ∧
        IsFinitePLBallPair ℝ d {p 0, p 1} ∧
        d ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = {p 0, p 1} ∧
        (∀ k, p k ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (a : Set E)))) ∧
        (R (p 0)).1 < (R (p 1)).1 ∧
        (polys i).boundary ℝ = R '' d ∪ segment ℝ (R (p 0)) (R (p 1)) ∧
        (R '' G.space) ∩ segment ℝ (R (p 0)) (R (p 1)) = {R (p 0), R (p 1)} ∧
        ∀ O : Set V3, IsOpen O → d ⊆ O →
          ∃ f : P2 → P2,
            FinitePiecewiseAffineOn f (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I) ∧
            InjOn f (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I) ∧
            MapsTo f (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I)
              (R '' convexHull ℝ (A '' (s : Set E))) ∧
            f (0, 0) = R (p 0) ∧ f (0, 1) = R (p 1) ∧
            (fun t : ℝ => f (0, t)) '' I = R '' d ∧
            (∀ z ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I,
              f z ∈ R '' (convexHull ℝ (A '' (s : Set E)) ∩ M.space) ↔ z.1 = 0) ∧
            (∀ c ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), (f (c, 0)).2 = 0 ∧ (f (c, 1)).2 = 0) ∧
            (∀ z ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I, F (f z) ∈ O ∩ interior J.space) ∧
            (∀ z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioo (0 : ℝ) 1,
              f z ∈ interior (R '' convexHull ℝ (A '' (s : Set E)))) ∧
            (∀ c ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
              (f (c, 0)).1 ∈ Ioo (0 : ℝ) 1 ∧ (f (c, 1)).1 ∈ Ioo (0 : ℝ) 1) ∧
            ∀ δ : ℝ, 0 < δ → ∃ c : ℝ,
              |c| < 1 / 2 ∧ |c| < δ ∧ c ≠ 0 ∧
              (f (c, 0)).1 < (R (p 0)).1 ∧ (R (p 1)).1 < (f (c, 1)).1 ∧
              FinitePiecewiseAffineOn (fun t : ℝ => f (c, t)) I ∧
              InjOn (fun t : ℝ => f (c, t)) I ∧
              IsFinitePLBallPair ℝ (segment ℝ (f (c, 0)) (f (c, 1))) {f (c, 0), f (c, 1)} ∧
              IsFinitePLBallPair ℝ ((fun t : ℝ => f (c, t)) '' I) {f (c, 0), f (c, 1)} ∧
              segment ℝ (f (c, 0)) (f (c, 1)) ∩ (R '' G.space) = {R (p 0), R (p 1)} ∧
              ((fun t : ℝ => f (c, t)) '' I) ∩ {z : P2 | z.2 = 0} = {f (c, 0), f (c, 1)} ∧
              Disjoint ((fun t : ℝ => f (c, t)) '' I)
                (R '' (convexHull ℝ (A '' (s : Set E)) ∩ M.space)) ∧
              ∃ axis : ↥(segment ℝ (f (c, 0)) (f (c, 1))) ≃ₜ
                ↥((fun t : ℝ => f (c, t)) '' I), axis.IsFinitePL ∧
                ∀ x : ↥(segment ℝ (f (c, 0)) (f (c, 1))),
                  (x : P2) ∈ ({f (c, 0), f (c, 1)} : Set P2) → (axis x : P2) = x := by
  classical
  obtain ⟨J, Pold, P₀, H, M, G, Phi, W, hbase, htubes⟩ :=
    exists_original_sphere_system_returning_component_tubes_with_other_faces S sS hdisjoint he K hK g hgc
      hgi hSV hs hs3 hedges hcofaces
      Q hQ A hmap hA hD hSD hε
  obtain ⟨hJ, hJcv, htriJ, hJQ, hPold, hPspace, hP₀, hP₀sub, hM, hMspace, hMJ,
    hMdim, hMpos, hG, hGspace, hGdim, hphysical, hPhival, hPhifix, hPhiPL, hPhiinv,
    hPhiS, hW, hDW, hfacesW, hfixW, hagree, hcofaces', hdisjoint', hinterior, hcrossings,
    hexterior, hfinite, hneigh, hmembers, hGunion, hdiscomponents, hcomponents⟩ := hbase
  have hedgeW (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card ≤ 2) :
      g '' convexHull ℝ (a : Set E) ⊆ W :=
    hfacesW a ha (by omega) (by intro h; subst a; omega)
  refine ⟨J, M, G, Phi, W, hJ, htriJ, hJQ, hM, hMJ, hG, hGspace, hGdim,
    hphysical, hPhifix, hPhiPL, hPhiinv, hPhiS, hW, hDW, hfacesW, hfixW, hagree,
    hcrossings, hinterior, hexterior, hfinite, ?_⟩
  intro a has ha2 hreturn
  let Iret := {C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent //
    (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
    Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
        convexHull ℝ (A '' (a : Set E))}
  change ∃ (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
    (n : Iret → ℕ) (labels : ∀ j, Fin (n j + 2) ≃ j.val)
    (polys : ∀ j, Polygon P2 (n j + 3)) (i : Iret) (p : Fin 2 → V3), _
  have hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) :=
    fun x hx => (hGspace.subset hx).2
  have hin (v : G.vertices) :
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := hinterior v v.property
  obtain ⟨F, R, n, labels, polys, hRF, hFR, hface, hbaseImage,
      hlabelsInj, hsegments, hpathup, hpathaxis, hpathdis, hRpaths, hFpaths,
      hballs, hleaves, hpolys, hpolysup, hboundaries, hFboundaries, hinside,
      i, hbigon, hbigonaxis, hinner, hinnermiss⟩ :=
    exists_original_triangle_returning_bigons K g hgi hs hs3 has ha2 Q A hmap hA G hG
      hGdim hGT hfinite hin hexterior hreturn
  let x : V3 := ((labels i 0).val : V3)
  let y : V3 := ((labels i (Fin.last (n i + 1))).val : V3)
  let d := i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
  have hdG : d ⊆ G.space := by
    intro z hz
    rw [hGunion]
    exact mem_iUnion.mpr ⟨i.val, hz⟩
  have hxyR : R x ≠ R y := by
    intro heq
    have hh := hlabelsInj i heq
    have := congrArg Fin.val hh
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  have hx0 : (R x).2 = 0 := ((hpathaxis i).symm.subset (by simp [x])).2
  have hy0 : (R y).2 = 0 := ((hpathaxis i).symm.subset (by simp [y])).2
  obtain ⟨p, hpair, hpne, hporder⟩ := exists_axis_ordered_endpoints R hxyR hx0 hy0
  have hdp : IsFinitePLBallPair ℝ d {p 0, p 1} := by
    rw [hpair]
    exact hballs i
  have hendsmem (k : Fin 2) : p k ∈ ({x, y} : Set V3) := by
    apply hpair.subset
    fin_cases k <;> simp
  have hpa (k : Fin 2) : p k ∈ convexHull ℝ (A '' (a : Set E)) := by
    apply i.property.2
    rw [hleaves i]
    exact hendsmem k
  have hpG (k : Fin 2) : p k ∈ G.space :=
    hdG (hdp.1 (by fin_cases k <;> simp))
  have haK : a ∈ K.faces := K.down_closed hs has (Finset.card_pos.mp (by omega))
  have hpedge (k : Fin 2) : p k ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (a : Set E))) :=
    original_returning_endpoint_mem_base_interior K g hgi hSV hs has ha2 Q A hmap hA
      G Phi (hedgeW a haK ha2.le) hagree hphysical (hpG k) (hpa k)
  have hind := affineIndependent_original_face_chart K g hgi hs Q A hmap hA
  have htne : (s.image A).Nonempty := Finset.image_nonempty.mpr (Finset.card_pos.mp (by omega))
  have hfront : d ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = {p 0, p 1} := by
    rw [hpair]
    have hh := G.actual_component_frontier_eq_degree_one_vertices hGdim (s.image A) htne
      (by
        change AffineIndependent ℝ ((↑) : ↥((s.image A : Finset V3) : Set V3) → V3)
        rw [Finset.coe_image]
        exact hind)
      (by simpa only [Finset.coe_image] using hGT)
      (by simpa only [Finset.coe_image] using hfinite)
      (by simpa only [Finset.coe_image] using hin)
      (by simpa only [Finset.coe_image] using hexterior) i.val
    simpa only [Finset.coe_image, hleaves i] using hh
  have hpolybd (j : Iret) : (polys j).boundary ℝ =
      R '' j.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∪
        segment ℝ (R ((labels j 0).val : V3)) (R ((labels j (Fin.last (n j + 1))).val : V3)) := by
    rw [hRpaths j]
    exact hboundaries j
  have hseg : segment ℝ (R (p 0)) (R (p 1)) = segment ℝ (R x) (R y) := by
    rw [← convexHull_pair, ← convexHull_pair]
    congr 1
    simpa only [image_pair] using congrArg (image R) hpair
  have hpoly : (polys i).boundary ℝ = R '' d ∪ segment ℝ (R (p 0)) (R (p 1)) := by
    rw [hseg]
    exact hpolybd i
  have hFRtri : EqOn (F ∘ R) id (convexHull ℝ (A '' (s : Set E))) :=
    hFR.mono (convexHull_subset_affineSpan _)
  have hupper (z : V3) (hz : z ∈ convexHull ℝ (A '' (s : Set E))) : 0 ≤ (R z).2 := by
    obtain ⟨w, hw, rfl⟩ := hface.symm.subset hz
    rw [hRF]
    have hsub : convexHull ℝ (range rightTriangle) ⊆ (univ : Set ℝ) ×ˢ Ici (0 : ℝ) := by
      apply convexHull_min ?_ ((convex_univ : Convex ℝ (univ : Set ℝ)).prod (convex_Ici 0))
      rintro _ ⟨j, rfl⟩
      fin_cases j <;> norm_num [rightTriangle]
    exact (hsub hw).2
  have hbaseaxis (z : V3) (hz : z ∈ convexHull ℝ (A '' (a : Set E))) : (R z).2 = 0 := by
    obtain ⟨w, hw, rfl⟩ := hbaseImage.symm.subset hz
    rw [hRF]
    exact Polygon.segment_subset_returning_axis (show (0, 0) ∈ {z : P2 | z.2 = 0} from rfl)
      (show (1, 0) ∈ {z : P2 | z.2 = 0} from rfl) hw
  have haxisbase (z : V3) (hz : z ∈ convexHull ℝ (A '' (s : Set E))) :
      (R z).2 = 0 ↔ z ∈ convexHull ℝ (A '' (a : Set E)) := by
    refine ⟨?_, hbaseaxis z⟩
    intro hzero
    obtain ⟨w, hw, rfl⟩ := hface.symm.subset hz
    rw [hRF] at hzero
    exact hbaseImage.subset ⟨w, right_triangle_axis_mem_base hw hzero, rfl⟩
  have hbasefront : convexHull ℝ (A '' (a : Set E)) ⊆
      intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) := by
    intro z hz
    have hztri := convexHull_mono (image_mono has) hz
    apply (affine_triangle_frontier_coordinates F R hRF hface hztri).mp
    obtain ⟨w, hw, heq⟩ := hface.symm.subset hztri
    have hRw : R z = w := by rw [← heq, hRF]
    rw [hRw]
    exact right_triangle_axis_mem_frontier hw (hRw ▸ hbaseaxis z hz)
  have hfiniteaxis := (projected_face_axis_contacts R hGT haxisbase hbasefront hfinite).2
  have hRiG : InjOn R G.space := by
    intro x hx y hy heq
    exact (hFRtri (hGT hx)).symm.trans ((congrArg F heq).trans (hFRtri (hGT hy)))
  let ends0 : Iret → P2 := fun j => if j = i then R (p 0) else R ((labels j 0).val : V3)
  let ends1 : Iret → P2 := fun j => if j = i then R (p 1) else R ((labels j (Fin.last (n j + 1))).val : V3)
  have hepairs (j : Iret) : ({ends0 j, ends1 j} : Set P2) =
      {R ((labels j 0).val : V3), R ((labels j (Fin.last (n j + 1))).val : V3)} := by
    by_cases hj : j = i
    · subst j
      simpa only [ends0, ends1, if_pos rfl, image_pair] using congrArg (image R) hpair
    · simp only [ends0, ends1, if_neg hj]
  have heseg (j : Iret) : segment ℝ (ends0 j) (ends1 j) =
      segment ℝ (R ((labels j 0).val : V3)) (R ((labels j (Fin.last (n j + 1))).val : V3)) := by
    rw [← convexHull_pair, ← convexHull_pair, hepairs j]
  have hRballs (j : Iret) : IsFinitePLBallPair ℝ
      (R '' j.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))) {ends0 j, ends1 j} := by
    rw [hepairs j]
    have hCG : j.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ G.space := by
      intro z hz
      rw [hGunion]
      exact mem_iUnion.mpr ⟨j.val, hz⟩
    simpa only [image_pair] using (hballs j).affine_image R (hRiG.mono hCG)
  have hRaxis (j : Iret) : (R '' j.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))) ∩
      {z : P2 | z.2 = 0} = {ends0 j, ends1 j} := by
    rw [hepairs j, hRpaths j]
    exact hpathaxis j
  have hcontacts : (R '' G.space) ∩ segment ℝ (R (p 0)) (R (p 1)) = {R (p 0), R (p 1)} := by
    have hh := actual_innermost_returning_base_contacts G hG hGdim (s.image A) htne
      (by
        change AffineIndependent ℝ ((↑) : ↥((s.image A : Finset V3) : Set V3) → V3)
        rw [Finset.coe_image]
        exact hind)
      (by simpa only [Finset.coe_image] using hGT)
      (by simpa only [Finset.coe_image] using hfinite)
      (by simpa only [Finset.coe_image] using hin)
      (by simpa only [Finset.coe_image] using hexterior)
      F R hRF (by simpa only [Finset.coe_image] using hface)
      (convexHull ℝ (A '' (a : Set E))) hbaseImage n polys ends0 ends1
      (fun j => (hpolys j).1) (fun j => (hpolys j).2) hpolysup
      (fun j => by rw [heseg j]; exact hpolybd j) hRballs hRaxis hinside i
      (by simpa only [ends0, ends1, if_pos rfl] using hporder) hinnermiss
    simpa only [ends0, ends1, if_pos rfl] using hh
  refine ⟨F, R, n, labels, polys, i, p, hRF, hFR, hface, hbaseImage, hpolys, hpolysup,
    hpolybd, hinner, hinnermiss, hbigon, hinside i, hdp, hfront, hpedge, hporder, hpoly, hcontacts, ?_⟩
  intro O hO hdO
  obtain ⟨Region, B, V, T, b, tube, hRegion, hdRegion, hdfront, hdinterior,
      hB, hBdis, hBT, hBM, hV, hT, hcover, hb, hb0, hb1, htube, haxis,
      hsheet0, hsheet1, hfrontier, hendbase, hendaxis, hmember⟩ :=
    htubes a has ha2 i.val p hpne hdp hfront hpedge O hO hdO
  obtain ⟨f, hf, hfi, hmapf, hfval, hfS, htraces, hfin, hstrands⟩ :=
    exists_planar_signed_tube_ribbon tube htube hsheet0 hsheet1 R F hFRtri
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hc0 : (0 : ℝ) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by norm_num
  have hfaxis (t : I) : f (0, t) = R (b t : V3) :=
    (hfval ⟨0, hc0⟩ t).trans (congrArg R (haxis t))
  have hfu : f (0, 0) = R (p 0) := (hfaxis ⟨0, le_rfl, zero_le_one⟩).trans (congrArg R hb0)
  have hfv : f (0, 1) = R (p 1) := (hfaxis ⟨1, zero_le_one, le_rfl⟩).trans (congrArg R hb1)
  have hcentral : (fun t : ℝ => f (0, t)) '' I = R '' d := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨b ⟨t, ht⟩, (b ⟨t, ht⟩).property, (hfaxis ⟨t, ht⟩).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨b.symm ⟨z, hz⟩, (b.symm ⟨z, hz⟩).property, ?_⟩
      exact (hfaxis _).trans (congrArg (fun y : d => R (y : V3)) (b.apply_symm_apply ⟨z, hz⟩))
  have hfends (c : ℝ) (hc : c ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      (f (c, 0)).2 = 0 ∧ (f (c, 1)).2 = 0 := by
    have hh (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) : (f (c, t)).2 = 0 := by
      rw [hfval ⟨c, hc⟩ t]
      have hd : (0, c) ∈ Dehn.signedTubeDiamond :=
        (Dehn.signedTubeDiamond_coordinate_iff (0, c)).mpr
          (by simpa using (abs_le.mpr hc).trans (show (1 / 2 : ℝ) ≤ 1 by norm_num))
      exact hendaxis R hbaseaxis ⟨((0, c), t), hd, t.property⟩
        ((Dehn.signedTubeSheet_coordinate_iff (0, c) hd 0).mpr (by simp)) ht
    exact ⟨hh ⟨0, le_rfl, zero_le_one⟩ (Or.inl rfl),
      hh ⟨1, zero_le_one, le_rfl⟩ (Or.inr rfl)⟩
  have hphys (z : P2) (hz : z ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I) :
      F (f z) ∈ O ∩ interior J.space := by
    have hd : (0, z.1) ∈ Dehn.signedTubeDiamond :=
      (Dehn.signedTubeDiamond_coordinate_iff (0, z.1)).mpr
        (by simpa using (abs_le.mpr hz.1).trans (show (1 / 2 : ℝ) ≤ 1 by norm_num))
    let zt : ↥(Dehn.signedTubeDiamond ×ˢ I) := ⟨((0, z.1), z.2), hd, hz.2⟩
    have hval' : f z = R (tube zt : V3) := hfval ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩
    have hsheet : (tube zt : V3) ∈ convexHull ℝ (A '' (s : Set E)) :=
      (hsheet0 zt).mp ((Dehn.signedTubeSheet_coordinate_iff (0, z.1) hd 0).mpr (by simp))
    have hFR' : F (R (tube zt : V3)) = (tube zt : V3) := hFRtri hsheet
    rw [hval', hFR']
    exact (hT (tube zt).property).2
  have hfbase (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1)
      (c : ℝ) (hc : c ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      f (c, t) ∈ Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ) := by
    have hd : (0, c) ∈ Dehn.signedTubeDiamond :=
      (Dehn.signedTubeDiamond_coordinate_iff (0, c)).mpr
        (by simpa using (abs_le.mpr hc).trans (show (1 / 2 : ℝ) ≤ 1 by norm_num))
    let zt : ↥(Dehn.signedTubeDiamond ×ˢ I) := ⟨((0, c), t), hd, t.property⟩
    have hbT := hendbase zt ((Dehn.signedTubeSheet_coordinate_iff (0, c) hd 0).mpr (by simp)) ht
    obtain ⟨w, hw, heq⟩ := hbaseImage.symm.subset hbT
    have hval' : f (c, t) = R (tube zt : V3) := hfval ⟨c, hc⟩ t
    rw [hval', ← heq, hRF]
    rw [← Polygon.returning_axis_segment (show ((0 : ℝ), (0 : ℝ)).2 = 0 from rfl)
      (show ((1 : ℝ), (0 : ℝ)).2 = 0 from rfl) zero_le_one]
    exact hw
  have hfopenbase (c : ℝ) (hc : c ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
      (f (c, 0)).1 ∈ Ioo (0 : ℝ) 1 ∧ (f (c, 1)).1 ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨ribbon_end_trace_mem_open_base (by norm_num) f hf hfi
      (show (0 : ℝ) ∈ I by simp) (hfbase ⟨0, le_rfl, zero_le_one⟩ (Or.inl rfl)) hc,
      ribbon_end_trace_mem_open_base (by norm_num) f hf hfi
      (show (1 : ℝ) ∈ I by simp) (hfbase ⟨1, zero_le_one, le_rfl⟩ (Or.inr rfl)) hc⟩
  refine ⟨f, hf, hfi, hmapf, hfu, hfv, hcentral, hfS, hfends, hphys, hfin, hfopenbase, ?_⟩
  intro δ hδ
  have hfup (z : P2) (hz : z ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I) : 0 ≤ (f z).2 := by
    obtain ⟨w, hw, heq⟩ := hmapf hz
    rw [← heq]
    exact hupper w hw
  have hfbd : (polys i).boundary ℝ = ((fun t : ℝ => f (0, t)) '' I) ∪
      segment ℝ (f (0, 0)) (f (0, 1)) := by rwa [hcentral, hfu, hfv]
  have hfo : (f (0, 0)).1 < (f (0, 1)).1 := by rwa [hfu, hfv]
  have hGM : R '' (convexHull ℝ (A '' (s : Set E)) ∩ M.space) = R '' G.space := by
    rw [hGspace, inter_comm]
  have hfiniteS : ((R '' (convexHull ℝ (A '' (s : Set E)) ∩ M.space)) ∩
      {z : P2 | z.2 = 0}).Finite := by rw [hGM]; exact hfiniteaxis
  have hcontactS : segment ℝ (f (0, 0)) (f (0, 1)) ∩
      (R '' (convexHull ℝ (A '' (s : Set E)) ∩ M.space)) = {f (0, 0), f (0, 1)} := by
    rw [hGM, hfu, hfv, inter_comm]
    exact hcontacts
  obtain ⟨c, hc, hcδ, hcne, hleft, hright, hwball, hball, hcontact, haxiscontact,
      hdis, axis, haxisPL, haxisfix⟩ :=
    exists_outer_ribbon_replacement_axis (show (0 : ℝ) < 1 / 2 by norm_num)
      f hf hfi hfup hfends hfS hfiniteS hcontactS (polys i) (hpolys i).1 (hpolys i).2
      (hpolysup i) hfbd hfo hδ
  simp only [hfu, hfv, hGM] at hleft hright hcontact
  obtain ⟨hstrandPL, hstrandInj, _⟩ := hstrands c (Ioo_subset_Icc_self hc)
  exact ⟨c, abs_lt.mpr hc, hcδ, hcne, hleft, hright, hstrandPL, hstrandInj,
    hwball, hball, hcontact, haxiscontact, hdis, axis, haxisPL, haxisfix⟩


theorem exists_original_sphere_system_returning_replacement_strands
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
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {D : Set X} (hD : IsClosed D) (hSD : Disjoint (⋃ i, S i) D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (J M G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) (W : Set X),
      J.faces.Finite ∧ convexHull ℝ (A '' (s : Set E)) ⊆ interior J.space ∧
      J.space ⊆ Q.target ∧ M.faces.Finite ∧ M.space ⊆ J.space ∧ G.faces.Finite ∧
      G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      Q.symm '' G.space = Phi '' (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      EqOn Phi id (Q.symm '' J.space)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ J.space, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ x ∈ M.space) ∧
      IsOpen W ∧ D ⊆ W ∧
      (∀ a ∈ K.faces, a.card ≤ 2 → g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      EqOn Phi id W ∧ Phi '' (⋃ i, S i) ∩ W = (⋃ i, S i) ∩ W ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) ∧
      (∀ w : G.vertices,
        (w : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet w).ncard = 1) ∧
      (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      ∀ a : Finset E, a ⊆ s → a.card = 2 →
      (∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
            convexHull ℝ (A '' (a : Set E))) →
      let Iret := {C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent //
        (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
            convexHull ℝ (A '' (a : Set E))}
      ∃ (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
        (n : Iret → ℕ) (labels : ∀ j, Fin (n j + 2) ≃ j.val)
        (polys : ∀ j, Polygon P2 (n j + 3)) (i : Iret) (p : Fin 2 → V3),
        let d := i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
        Function.LeftInverse R F ∧ EqOn (F ∘ R) id (affineSpan ℝ (A '' (s : Set E))) ∧
        F '' convexHull ℝ (range rightTriangle) = convexHull ℝ (A '' (s : Set E)) ∧
        F '' segment ℝ (0, 0) (1, 0) = convexHull ℝ (A '' (a : Set E)) ∧
        (∀ j, (polys j).HasSimplicialEdges ∧ Function.Injective (polys j)) ∧
        (∀ j k, 0 ≤ (polys j k).2) ∧
        (∀ j, (polys j).boundary ℝ =
          R '' j.val.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∪
          segment ℝ (R ((labels j 0).val : V3))
            (R ((labels j (Fin.last (n j + 1))).val : V3))) ∧
        closure (polys i).inside ∩ (⋃ j, (polys j).boundary ℝ) = (polys i).boundary ℝ ∧
        Disjoint (polys i).inside (⋃ j, (polys j).boundary ℝ) ∧
        IsFinitePLBallPair P2 (closure (polys i).inside) ((polys i).boundary ℝ) ∧
        closure (polys i).inside ⊆ convexHull ℝ (range rightTriangle) ∧
        IsFinitePLBallPair ℝ d {p 0, p 1} ∧
        d ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = {p 0, p 1} ∧
        (∀ k, p k ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (a : Set E)))) ∧
        (R (p 0)).1 < (R (p 1)).1 ∧
        (polys i).boundary ℝ = R '' d ∪ segment ℝ (R (p 0)) (R (p 1)) ∧
        (R '' G.space) ∩ segment ℝ (R (p 0)) (R (p 1)) = {R (p 0), R (p 1)} ∧
        ∀ O : Set V3, IsOpen O → d ⊆ O →
          ∃ f : P2 → P2,
            FinitePiecewiseAffineOn f (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I) ∧
            InjOn f (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I) ∧
            MapsTo f (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I)
              (R '' convexHull ℝ (A '' (s : Set E))) ∧
            f (0, 0) = R (p 0) ∧ f (0, 1) = R (p 1) ∧
            (fun t : ℝ => f (0, t)) '' I = R '' d ∧
            (∀ z ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I,
              f z ∈ R '' (convexHull ℝ (A '' (s : Set E)) ∩ M.space) ↔ z.1 = 0) ∧
            (∀ c ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), (f (c, 0)).2 = 0 ∧ (f (c, 1)).2 = 0) ∧
            (∀ z ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I, F (f z) ∈ O ∩ interior J.space) ∧
            (∀ z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioo (0 : ℝ) 1,
              f z ∈ interior (R '' convexHull ℝ (A '' (s : Set E)))) ∧
            (∀ c ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
              (f (c, 0)).1 ∈ Ioo (0 : ℝ) 1 ∧ (f (c, 1)).1 ∈ Ioo (0 : ℝ) 1) ∧
            ∀ δ : ℝ, 0 < δ → ∃ c : ℝ,
              |c| < 1 / 2 ∧ |c| < δ ∧ c ≠ 0 ∧
              (f (c, 0)).1 < (R (p 0)).1 ∧ (R (p 1)).1 < (f (c, 1)).1 ∧
              FinitePiecewiseAffineOn (fun t : ℝ => f (c, t)) I ∧
              InjOn (fun t : ℝ => f (c, t)) I ∧
              IsFinitePLBallPair ℝ (segment ℝ (f (c, 0)) (f (c, 1))) {f (c, 0), f (c, 1)} ∧
              IsFinitePLBallPair ℝ ((fun t : ℝ => f (c, t)) '' I) {f (c, 0), f (c, 1)} ∧
              segment ℝ (f (c, 0)) (f (c, 1)) ∩ (R '' G.space) = {R (p 0), R (p 1)} ∧
              ((fun t : ℝ => f (c, t)) '' I) ∩ {z : P2 | z.2 = 0} = {f (c, 0), f (c, 1)} ∧
              Disjoint ((fun t : ℝ => f (c, t)) '' I)
                (R '' (convexHull ℝ (A '' (s : Set E)) ∩ M.space)) ∧
              ∃ axis : ↥(segment ℝ (f (c, 0)) (f (c, 1))) ≃ₜ
                ↥((fun t : ℝ => f (c, t)) '' I), axis.IsFinitePL ∧
                ∀ x : ↥(segment ℝ (f (c, 0)) (f (c, 1))),
                  (x : P2) ∈ ({f (c, 0), f (c, 1)} : Set P2) → (axis x : P2) = x := by
  obtain ⟨J, M, G, Phi, W, hJ, htriJ, hJQ, hM, hMJ, hG, hGspace, hGdim,
      hphysical, hPhifix, hPhiPL, hPhiinv, hPhiS, hW, hDW, hfacesW, hfixW, hagree, _, hrest⟩ :=
    exists_original_sphere_system_returning_replacement_strands_with_other_faces S sS hdisjoint he K hK g hgc hgi hSV hs hs3 hedges hcofaces
      Q hQ A hmap hA hD hSD hε
  refine ⟨J, M, G, Phi, W, hJ, htriJ, hJQ, hM, hMJ, hG, hGspace, hGdim,
      hphysical, hPhifix, hPhiPL, hPhiinv, hPhiS, hW, hDW, ?_, hfixW, hagree, hrest⟩
  intro a ha ha2
  exact hfacesW a ha (by omega) (by intro h; subst a; omega)

end PoincareConjecture.M76
