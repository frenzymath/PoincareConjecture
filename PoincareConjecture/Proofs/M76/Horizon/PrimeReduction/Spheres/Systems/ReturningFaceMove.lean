import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ReturningReplacementAxis
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.OriginalFaceAxisMove
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.FaceRibbonConfinement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.OriginalSkeletonContactCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.SupportedEdgeCofaceTransport

set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_original_protected_sphere_system_returning_face_move_with_other_faces
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {K N : SimplicialComplex ℝ E} (hK : K.faces.Finite) (hNK : N ≤ K)
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
    ∃ (G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X),
      G.faces.Finite ∧ G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) ∧
      (∀ w : G.vertices,
        (w : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet w).ncard = 1) ∧
      (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      Q.symm '' G.space = Phi '' (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn Phi id Z ∧ EqOn Phi id (g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card ≤ 2 →
        (g '' convexHull ℝ (a : Set E)) ∩ (Phi '' (⋃ i, S i)) =
          (g '' convexHull ℝ (a : Set E)) ∩ (⋃ i, S i)) ∧
      (∃ W : Set X, IsOpen W ∧ Z ∪ g '' K.vertices ⊆ W ∧
        (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s → g '' convexHull ℝ (a : Set E) ⊆ W) ∧
        EqOn Phi id W) ∧
      (∀ w ∈ G.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
        ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 ((ℝ × ℝ) × ℝ),
            w ∈ B.source ∧ B.source ⊆ O ∩ Q.target ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source,
              x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0) ∧
      ∀ a : Finset E, a ⊆ s → a.card = 2 →
      (∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
            convexHull ℝ (A '' (a : Set E))) →
      let edge := g '' convexHull ℝ (a : Set E)
      ∃ (H : X ≃ₜ X) (C U : Set X) (x y : X),
        x ≠ y ∧ x ∈ edge ∩ (⋃ i, S i) ∧ y ∈ edge ∩ (⋃ i, S i) ∧
        IsOpen U ∧ IsCompact C ∧ C ⊆ U ∧
        Disjoint U Z ∧ Disjoint U (g '' K.vertices) ∧
        (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
          Disjoint U (g '' convexHull ℝ (t : Set E))) ∧
        (∀ z ∉ C, H z = z) ∧ (∀ z ∉ U, H z = z) ∧
        (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        edge ∩ (H.symm '' (Phi '' (⋃ i, S i))) = (edge ∩ (⋃ i, S i)) \ {x, y} ∧
        (edge ∩ (H.symm '' (Phi '' (⋃ i, S i)))).ncard = (edge ∩ (⋃ i, S i)).ncard - 2 ∧
        EqOn H id Z ∧ EqOn H id (g '' K.vertices) ∧
        (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
          (g '' convexHull ℝ (t : Set E)) ∩ (H.symm '' (Phi '' (⋃ i, S i))) =
            (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)) ∧
        (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
          ((g '' convexHull ℝ (t : Set E)) ∩ (H.symm '' (Phi '' (⋃ i, S i)))).ncard =
            ((g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)).ncard) ∧
        ((⋃ t : K.FaceOfCard 2, g '' convexHull ℝ (t.1 : Set E)) ∩
          (H.symm '' (Phi '' (⋃ i, S i)))).ncard + 2 =
          ((⋃ t : K.FaceOfCard 2, g '' convexHull ℝ (t.1 : Set E)) ∩ (⋃ i, S i)).ncard ∧
        ∀ i, ∀ t ∈ K.faces, t.card = 2 →
          HasOriginalEdgeCofaceCharts e (H.symm '' (Phi '' S i)) K g t := by
  classical
  have hD : IsClosed (Z ∪ g '' K.vertices) :=
    hZ.union ((K.finite_vertices_of_finite_faces hK).image g).isClosed
  have hSD : Disjoint (⋃ i, S i) (Z ∪ g '' K.vertices) := disjoint_union_right.mpr ⟨hSZ, hSV⟩
  obtain ⟨J, M, G, Phi, W, hJ, htriJ, hJQ, hM, hMJ, hG, hGspace, hGdim,
      hphysical, hPhifix, hPhiPL, hPhiinv, hPhiS, hW, hDW, hfacesW, hfixW, hagree,
      hcrossings, hinterior, hexterior, hfinite, hreturn⟩ :=
    exists_original_sphere_system_returning_replacement_strands_with_other_faces S sS hdis he K hK g hgc hgi hSV hs hs3 hedges
      hcofaces Q hQ A hmap hA hD hSD hε
  have hedgeW (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card ≤ 2) :
      g '' convexHull ℝ (a : Set E) ⊆ W :=
    hfacesW a ha (by omega) (by intro h; subst a; omega)
  have hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) := fun x hx => (hGspace.subset hx).2
  have hPhiZ : EqOn Phi id Z := hfixW.mono (subset_union_left.trans hDW)
  have hPhiV : EqOn Phi id (g '' K.vertices) := hfixW.mono (subset_union_right.trans hDW)
  have hedgeAgree (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card ≤ 2) :
      (g '' convexHull ℝ (a : Set E)) ∩ (Phi '' (⋃ i, S i)) = (g '' convexHull ℝ (a : Set E)) ∩ (⋃ i, S i) := by
    ext x
    constructor
    · rintro ⟨hx, hxS⟩
      exact ⟨hx, (hagree.subset ⟨hxS, hedgeW a ha ha2 hx⟩).1⟩
    · rintro ⟨hx, hxS⟩
      exact ⟨hx, (hagree.symm.subset ⟨hxS, hedgeW a ha ha2 hx⟩).1⟩
  have hSigmaZ : Disjoint (Phi '' (⋃ i, S i)) Z := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hz
    have hfix : Phi (Phi x) = Phi x := hPhiZ hz
    have heq : Phi x = x := Phi.injective hfix
    exact disjoint_left.mp hSZ hx (heq ▸ hz)
  have hPhiCofaces (i : κ) (t : Finset E) (ht : t ∈ K.faces) (ht2 : t.card = 2) :
      HasOriginalEdgeCofaceCharts e (Phi '' S i) K g t := by
    apply (hcofaces i t ht ht2).image_of_disjoint_support Phi hW.isClosed_compl
    · exact disjoint_left.mpr (fun x hx hxedge => hx (hedgeW t ht ht2.le hxedge))
    · simpa only [compl_compl] using hfixW
  have hphysicalCrossings : ∀ w ∈ G.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
        ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 ((ℝ × ℝ) × ℝ),
            w ∈ B.source ∧ B.source ⊆ O ∩ Q.target ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source,
              x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0 := by
    intro w hw O hO hwO
    have hwJ : w ∈ interior J.space := htriJ (intrinsicInterior_subset hw.2)
    obtain ⟨B, hwB, hBO, hBw, hBPL, hBinv, hBM, hBT⟩ :=
      hcrossings w ⟨(hGspace.subset hw.1).1, hw.2⟩
        (O ∩ interior J.space) (hO.inter isOpen_interior) ⟨hwO, hwJ⟩
    refine ⟨B, hwB, (fun x hx => ⟨(hBO hx).1, hJQ (interior_subset (hBO hx).2)⟩),
      hBw, hBPL, hBinv, ?_, hBT⟩
    intro x hx
    exact (hPhiS x (interior_subset (hBO hx).2)).trans (hBM x hx)
  refine ⟨G, Phi, hG, hGT, hGdim, hinterior, hexterior, hfinite,
    hphysical, hPhiPL, hPhiinv, hPhiZ, hPhiV,
    hedgeAgree, ⟨W, hW, hDW, hfacesW, hfixW⟩, hphysicalCrossings, ?_⟩
  intro a has ha2 hret
  have ha : a ∈ K.faces := K.down_closed hs has (Finset.card_pos.mp (by omega))
  obtain ⟨F, R, n, labels, polys, i, p, hRF, hFR, hface, hbase, hpolys, hpolysup,
      hpolybd, hinner, hinnermiss, hbigon, hinside, hdp, hfront, hpedge, hporder,
      hpoly, hcontacts, hribbons⟩ := hreturn a has ha2 hret
  obtain ⟨f, hf, hfi, hmapf, hfu, hfv, hcentral, hfS, hfends, hphys, hfin,
      hfopenbase, hstrands⟩ := hribbons univ isOpen_univ (subset_univ _)
  obtain ⟨c, hc, hcsmall, hcne, hleft, hright, hstrandPL, hstrandInj, hwball,
      hstrandball, hnewcontacts, haxiscontact, havoid, axis, haxisPL, haxisfix⟩ :=
    hstrands 1 zero_lt_one
  have hcopen : c ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := abs_lt.mp hc
  have hcclosed := Ioo_subset_Icc_self hcopen
  have hFRtri : EqOn (F ∘ R) id (convexHull ℝ (A '' (s : Set E))) :=
    hFR.mono (convexHull_subset_affineSpan _)
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hgi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      (Q.injOn (hmap hx) (hmap hy) ((hA hx).trans (hxy.trans (hA hy).symm)))
  have hAsp := A.toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) (K.nonempty_of_mem_faces hs).to_set.convexHull hAi
  have hAap := hAsp.mono (affineSpan_mono ℝ (convexHull_mono has))
  have haInterior : intrinsicInterior ℝ (convexHull ℝ (A '' (a : Set E))) =
      A '' intrinsicInterior ℝ (convexHull ℝ (a : Set E)) := by
    change intrinsicInterior ℝ (convexHull ℝ (A.toAffineMap '' (a : Set E))) =
      A.toAffineMap '' intrinsicInterior ℝ (convexHull ℝ (a : Set E))
    rw [← A.toAffineMap.image_convexHull]
    exact A.toAffineMap.intrinsicInterior_image_of_injOn_span _ hAap
  have hpa (k : Fin 2) : p k ∈ convexHull ℝ (A '' (a : Set E)) := intrinsicInterior_subset (hpedge k)
  have hpT (k : Fin 2) : p k ∈ convexHull ℝ (A '' (s : Set E)) :=
    convexHull_mono (image_mono has) (hpa k)
  have hpG (k : Fin 2) : p k ∈ G.space := by
    have hpR : R (p k) ∈ R '' G.space := (hcontacts.symm.subset (by fin_cases k <;> simp)).1
    obtain ⟨y, hy, heq⟩ := hpR
    have hyp : y = p k := (hFRtri (hGT hy)).symm.trans
      ((congrArg F heq).trans (hFRtri (hpT k)))
    exact hyp ▸ hy
  have hpinverse (k : Fin 2) : ∃ u ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set E)),
      A u = p k ∧ g u = Q.symm (p k) := by
    obtain ⟨u, hu, heq⟩ := haInterior.subset (hpedge k)
    refine ⟨u, hu, heq, ?_⟩
    have hus := convexHull_mono has (intrinsicInterior_subset hu)
    rw [← heq, ← hA hus]
    exact (Q.left_inv (hmap hus)).symm
  have hpSigma (k : Fin 2) : Q.symm (p k) ∈ Phi '' (⋃ i, S i) :=
    (hphysical.subset ⟨p k, hpG k, rfl⟩).1
  have hpEdge (k : Fin 2) : Q.symm (p k) ∈ g '' convexHull ℝ (a : Set E) := by
    obtain ⟨u, hu, _, heq⟩ := hpinverse k
    exact ⟨u, intrinsicInterior_subset hu, heq⟩
  have hpOriginal (k : Fin 2) : Q.symm (p k) ∈ (g '' convexHull ℝ (a : Set E)) ∩ (⋃ i, S i) :=
    (hedgeAgree a ha ha2.le).subset ⟨hpEdge k, hpSigma k⟩
  obtain ⟨u, hu, huA, huQ⟩ := hpinverse 0
  have huZ : g u ∉ Z := fun hz => disjoint_left.mp hSigmaZ (huQ.symm ▸ hpSigma 0) hz
  have hFW : F '' ((fun t : ℝ => f (c, t)) '' I) ⊆
      A '' (intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∪
        intrinsicInterior ℝ (convexHull ℝ (a : Set E))) := by
    have hbase' : F '' (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)) =
        convexHull ℝ (A '' (a : Set E)) := by
      rw [← Polygon.returning_axis_segment
        (show ((0 : ℝ), (0 : ℝ)).2 = 0 from rfl)
        (show ((1 : ℝ), (0 : ℝ)).2 = 0 from rfl) zero_le_one]
      exact hbase
    have hh := mapsTo_returning_strand_original_face_interiors K g hgi hs has Q A hmap hA
      F R hRF hFRtri hbase' f c (fun t ht => hfin (c, t) ⟨hcopen, ht⟩)
      (by
        intro t ht
        rcases ht with ht | ht
        · subst t
          exact ⟨(hfopenbase c hcopen).1, (hfends c hcclosed).1⟩
        · rw [mem_singleton_iff] at ht
          subst t
          exact ⟨(hfopenbase c hcopen).2, (hfends c hcclosed).2⟩)
    exact image_subset_iff.mpr hh
  have hup : ∀ z ∈ ((fun t : ℝ => f (c, t)) '' I), 0 ≤ z.2 := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨y, hy, heq⟩ := hmapf
      (show (c, t) ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ I from ⟨hcclosed, ht⟩)
    obtain ⟨z, hz, rfl⟩ := hface.symm.subset hy
    rw [hRF] at heq
    change 0 ≤ (f (c, t)).2
    rw [← heq]
    exact ((mem_right_region_iff z).mp hz).2.1
  have hpq : (f (c, 0)).1 < (f (c, 1)).1 := lt_trans hleft (lt_trans hporder hright)
  have hGM : R '' (convexHull ℝ (A '' (s : Set E)) ∩ M.space) = R '' G.space := by
    rw [hGspace, inter_comm]
  rw [hGM] at havoid
  have hcontact : (R '' G.space) ∩ segment ℝ (f (c, 0)) (f (c, 1)) =
      {R (p 0), R (p 1)} := by rwa [inter_comm]
  have hcd : R (p 0) ≠ R (p 1) := fun heq => hporder.ne (congrArg Prod.fst heq)
  have hfiniteSigma : ((g '' convexHull ℝ (a : Set E)) ∩ (Phi '' (⋃ i, S i))).Finite := by
    rw [hedgeAgree a ha ha2.le, inter_comm]
    exact hedges a ha ha2
  obtain ⟨H, C, U, hU, hC, hCU, hUZ, hUV, hUother, hHC, hHU, hHPL, hHinv,
      hfix, himage, hexact, hdrop, hHZ, hHV, hother, hothercard, hCedge, hnewC⟩ :=
    exists_original_face_axis_move_with_edge_support e he hK hNK g hgc hgi hZ hmark hs ha hs3 ha2 has
      hu huZ Q hQ A hmap hA F R hRF hFR hface hbase hstrandball hpq
      (hfends c hcclosed).1 (hfends c hcclosed).2 hup haxiscontact hFW G hGT
      hphysical havoid hcontact hcd hfiniteSigma
  have hjp (k : Fin 2) : Q.symm (F (R (p k))) = Q.symm (p k) := congrArg Q.symm (hFRtri (hpT k))
  have hpphysical : Q.symm (p 0) ≠ Q.symm (p 1) := by
    intro heq
    have hpQ (k : Fin 2) : p k ∈ Q.target := hJQ (hMJ ((hGspace.subset (hpG k)).1))
    exact hcd (congrArg R (Q.symm.injOn (hpQ 0) (hpQ 1) heq))
  simp only [hjp] at hexact
  rw [hedgeAgree a ha ha2.le] at hexact hdrop
  have hotherOriginal (t : Finset E) (ht : t ∈ K.faces) (ht2 : t.card ≤ 2) (hta : t ≠ a) :
      (g '' convexHull ℝ (t : Set E)) ∩ (H.symm '' (Phi '' (⋃ i, S i))) =
        (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i) :=
    (hother t ht ht2 hta).trans (hedgeAgree t ht ht2)
  have hnewSV : Disjoint (H.symm '' (Phi '' (⋃ i, S i))) (g '' K.vertices) := by
    apply disjoint_left.mpr
    rintro z ⟨y, ⟨x, hx, rfl⟩, heq⟩ hz
    have heq' := congrArg H heq
    simp only [H.apply_symm_apply, hHV hz, id_eq] at heq'
    have hxz : x = z := Phi.injective (heq'.trans (hPhiV hz).symm)
    exact disjoint_left.mp hSV hx (hxz.symm ▸ hz)
  refine ⟨H, C, U, Q.symm (p 0), Q.symm (p 1), hpphysical, hpOriginal 0, hpOriginal 1,
    hU, hC, hCU, hUZ, hUV, hUother, hHC, hHU, hHPL, hHinv, hexact, hdrop,
    hHZ, hHV, hotherOriginal, ?_, ?_, ?_⟩
  · intro t ht ht2 hta
    rw [hotherOriginal t ht ht2 hta]
  · apply ncard_original_skeleton_contacts_remove_pair K hK g hgi
      (⋃ i, S i) (H.symm '' (Phi '' (⋃ i, S i))) hSV hnewSV
      (fun t => by simpa only [inter_comm] using hedges t.1 t.2.1 t.2.2)
      ⟨a, ha, ha2⟩ hpphysical (hpOriginal 0) (hpOriginal 1) hexact
    intro t hta
    exact hotherOriginal t.1 t.2.1 t.2.2.le (fun h => hta (Subtype.ext h))
  · intro i t ht ht2
    apply (hPhiCofaces i t ht ht2).image_of_disjoint_contact_support H.symm hC.isClosed
    · apply disjoint_left.mpr
      rintro z hzC ⟨hzS, hzt⟩
      by_cases hta : t = a
      · subst t
        exact disjoint_left.mp hnewC hzC ⟨hzt,
          image_mono (image_mono (subset_iUnion S i)) hzS⟩
      · exact disjoint_left.mp (hUother t ht ht2.le hta) (hCU hzC) hzt
    · intro z hz
      apply H.injective
      change H (H.symm z) = H z
      rw [H.apply_symm_apply, hHC z hz]

theorem exists_original_protected_sphere_system_returning_face_move
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {K N : SimplicialComplex ℝ E} (hK : K.faces.Finite) (hNK : N ≤ K)
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
    ∃ (G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X),
      G.faces.Finite ∧ G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) ∧
      (∀ w : G.vertices,
        (w : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet w).ncard = 1) ∧
      (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      Q.symm '' G.space = Phi '' (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn Phi id Z ∧ EqOn Phi id (g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card ≤ 2 →
        (g '' convexHull ℝ (a : Set E)) ∩ (Phi '' (⋃ i, S i)) =
          (g '' convexHull ℝ (a : Set E)) ∩ (⋃ i, S i)) ∧
      (∃ W : Set X, IsOpen W ∧ Z ∪ g '' K.vertices ⊆ W ∧
        (∀ a ∈ K.faces, a.card ≤ 2 → g '' convexHull ℝ (a : Set E) ⊆ W) ∧
        EqOn Phi id W) ∧
      ∀ a : Finset E, a ⊆ s → a.card = 2 →
      (∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
            convexHull ℝ (A '' (a : Set E))) →
      let edge := g '' convexHull ℝ (a : Set E)
      ∃ (H : X ≃ₜ X) (C U : Set X) (x y : X),
        x ≠ y ∧ x ∈ edge ∩ (⋃ i, S i) ∧ y ∈ edge ∩ (⋃ i, S i) ∧
        IsOpen U ∧ IsCompact C ∧ C ⊆ U ∧
        Disjoint U Z ∧ Disjoint U (g '' K.vertices) ∧
        (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
          Disjoint U (g '' convexHull ℝ (t : Set E))) ∧
        (∀ z ∉ C, H z = z) ∧ (∀ z ∉ U, H z = z) ∧
        (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        edge ∩ (H.symm '' (Phi '' (⋃ i, S i))) = (edge ∩ (⋃ i, S i)) \ {x, y} ∧
        (edge ∩ (H.symm '' (Phi '' (⋃ i, S i)))).ncard = (edge ∩ (⋃ i, S i)).ncard - 2 ∧
        EqOn H id Z ∧ EqOn H id (g '' K.vertices) ∧
        (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
          (g '' convexHull ℝ (t : Set E)) ∩ (H.symm '' (Phi '' (⋃ i, S i))) =
            (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)) ∧
        (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
          ((g '' convexHull ℝ (t : Set E)) ∩ (H.symm '' (Phi '' (⋃ i, S i)))).ncard =
            ((g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)).ncard) ∧
        ((⋃ t : K.FaceOfCard 2, g '' convexHull ℝ (t.1 : Set E)) ∩
          (H.symm '' (Phi '' (⋃ i, S i)))).ncard + 2 =
          ((⋃ t : K.FaceOfCard 2, g '' convexHull ℝ (t.1 : Set E)) ∩ (⋃ i, S i)).ncard ∧
        ∀ i, ∀ t ∈ K.faces, t.card = 2 →
          HasOriginalEdgeCofaceCharts e (H.symm '' (Phi '' S i)) K g t := by
  obtain ⟨G, Phi, hG, hGT, hGdim, hinterior, hexterior, hfinite,
      hphysical, hPhiPL, hPhiinv, hPhiZ, hPhiV, hedgeAgree, hfixed, _, hreturn⟩ :=
    exists_original_protected_sphere_system_returning_face_move_with_other_faces S sS hdis he hK hNK g hgc hgi hZ hmark hSZ hSV hs hs3
      hedges hcofaces Q hQ A hmap hA hε
  obtain ⟨W, hW, hDW, hfacesW, hfixW⟩ := hfixed
  refine ⟨G, Phi, hG, hGT, hGdim, hinterior, hexterior, hfinite,
      hphysical, hPhiPL, hPhiinv, hPhiZ, hPhiV, hedgeAgree, ⟨W, hW, hDW, ?_, hfixW⟩, hreturn⟩
  intro a ha ha2
  exact hfacesW a ha (by omega) (by intro h; subst a; omega)

end PoincareConjecture.M76
