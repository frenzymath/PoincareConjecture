import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeModel
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars
import PoincareConjecture.Proofs.M76.Wall.OriginalInteriorVertexDual
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLConicalHalfBlocks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import PoincareConjecture.Proofs.M76.Wall.OriginalInteriorEdgeDual
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcDualBoundaryAvoidance
import PoincareConjecture.Proofs.M76.Wall.Mathlib.DualStrictCoface
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedStarDualInterval
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.MaximalFaceDual
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBirthStar
import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetChartSigns

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in

theorem exists_original_signed_tube_joint_intervals
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (hAF : (A ∩ frontier R).Finite)
    (S : Fin 2 → Set X) (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (F : X → E) (hF : Continuous F) (H : C ≃ₜ K.space)
    (hH : ∀ x : C, (H x : E) = F x) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K)
    (hfull : ∀ i t, t ∈ K.faces → (∀ v ∈ t, v ∈ (M i).vertices) → t ∈ (M i).faces)
    (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space →
      (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source → (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
    (s : Finset E) (hs : s ∈ (M arc).faces) (hcard : s.card = 2) :
    let J := K.barycentricDualBlock s
    let m := s.centroid ℝ id
    let q := (J.link m).space
    ∃ p : (M arc).vertices, (p : E) ∈ s ∧ (g p : X) ∈ interior R ∧
      IsFinitePLBallPair P2 J.space q ∧
      MapsTo (fun z => (g z : X)) J.space (interior R) ∧
      J.space = ((M reg).barycentricDualBlock s).space ∧
      Disjoint J.space (M fr).space ∧ J.space ∩ (M arc).space = {m} ∧
      (∀ v ∈ s, J.space ⊆ ((K.barycentricDualBlock {v}).link v).space) ∧
      ∃ t u : Fin 2 → Finset E, ∀ i : Fin 2,
        t i ∈ (M (sheet i)).faces ∧ u i ∈ (M (sheet i)).faces ∧
        s ⊆ t i ∧ s ⊆ u i ∧ (t i).card = 3 ∧ (u i).card = 3 ∧ t i ≠ u i ∧
        (∀ v ∈ (M (sheet i)).faces, s ⊆ v → v.card = 3 → v = t i ∨ v = u i) ∧
        let I := ((M (sheet i)).barycentricDualBlock s).space
        let a := (t i).centroid ℝ id
        let b := (u i).centroid ℝ id
        I = J.space ∩ (M (sheet i)).space ∧
        IsFinitePLBallPair ℝ I {a, b} ∧ m ∈ I \ {a, b} ∧
        I ∩ q = {a, b} ∧
        J.space ∩ {z | B p (g z) i.castSucc = 0} = I ∧
        q ∩ {z | B p (g z) i.castSucc = 0} = {a, b} ∧
        B p (g a) i.rev.castSucc < 0 ∧ 0 < B p (g b) i.rev.castSucc := by
  classical
  let J := K.barycentricDualBlock s
  let m := s.centroid ℝ id
  let q := (J.link m).space
  have hsK : s ∈ K.faces := hMK arc hs
  have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
    rw [← hH (g z)]
    have he : g z = H.symm ⟨z, hz⟩ := Subtype.ext (hg ⟨z, hz⟩)
    rw [he, H.apply_symm_apply]
  have hgF (x : X) (hx : x ∈ C) : (g (F x) : X) = x := by
    have he := hg (H ⟨x, hx⟩)
    simpa only [hH, H.symm_apply_apply] using he
  have hFK (x : X) (hx : x ∈ C) : F x ∈ K.space := hH ⟨x, hx⟩ ▸ (H ⟨x, hx⟩).property
  have hfinite : ((M arc).space ∩ (M fr).space).Finite := by
    apply (hAF.image F).subset
    intro z hz
    have hzK := space_subset_of_le (hMK arc) hz.1
    exact ⟨g z, ⟨(harc z hzK).mp hz.1, (hfr z hzK).mp hz.2⟩, hFg z hzK⟩
  obtain ⟨hmiss, p0, hps, hpFr⟩ := K.arc_edge_dual_disjoint_boundary
    (M arc) (M fr) (hMK arc) (hMK fr) (hfull fr) hfinite hs hcard
  have hpAvertex := (M arc).face_subset_vertices hs hps
  let p : (M arc).vertices := ⟨p0, hpAvertex⟩
  have hpK : p0 ∈ K.vertices := hMK arc hpAvertex
  have hpA : (g p0 : X) ∈ A :=
    (harc p0 (K.vertices_subset_space hpK)).mp ((M arc).vertices_subset_space hpAvertex)
  have hvertex (i : κ) {z : E} (hzK : z ∈ K.vertices) (hzi : z ∈ (M i).space) :
      z ∈ (M i).vertices := by
    obtain ⟨v, hv, hzv⟩ := mem_space_iff.mp hzi
    exact (M i).face_subset_vertices hv ((K.vertex_mem_convexHull_iff hzK (hMK i hv)).mp hzv)
  have hpR : (g p0 : X) ∈ interior R := by
    by_contra hn
    have hpfront : (g p0 : X) ∈ frontier R := ⟨subset_closure (hAR hpA), hn⟩
    exact hpFr (hvertex fr hpK ((hfr p0 (K.vertices_subset_space hpK)).mpr hpfront))
  obtain ⟨hsource, hface, haxis, hsheets⟩ := hB p
  have hpstar : p0 ∈ (K.closedStar p0).space := by
    apply vertices_subset_space
    exact ⟨hpK, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p0)]
      using (show {p0} ∈ K.faces from hpK)⟩
  have hpzero := ((haxis (g p0) (hsource hpstar)).mp hpA).2
  have hstarK : (K.closedStar p0).space ⊆ K.space := space_subset_of_le (fun _ hv => hv.1)
  have hJball : IsFinitePLBallPair P2 J.space q :=
    isFinitePLBallPair_original_interior_edge_dual K H g hg hsK hcard hps
      (hAC hpA) (B p) hsource hface
  have hJK : J.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le s)).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hmJ : m ∈ J.space :=
    J.vertices_subset_space (K.faceCentroid_mem_barycentricDualBlock_vertices hsK)
  have hmA : (g m : X) ∈ A := (harc m (hJK hmJ)).mp
    ((M arc).convexHull_subset_space hs
      (s.centroid_mem_convexHull ((M arc).nonempty_of_mem_faces hs)))
  have hmR : (g m : X) ∈ interior R := by
    by_contra hn
    exact disjoint_left.mp hmiss hmJ ((hfr m (hJK hmJ)).mpr ⟨subset_closure (hAR hmA), hn⟩)
  have hJR : MapsTo (fun z => (g z : X)) J.space (interior R) := by
    have hc := hJball.isConnected.isPreconnected.image (fun z => (g z : X))
      (hgPL.continuousOn.mono hJK)
    have hd : Disjoint (frontier (interior R)) ((fun z => (g z : X)) '' J.space) := by
      apply disjoint_left.mpr
      rintro _ hz ⟨w, hw, rfl⟩
      exact disjoint_left.mp hmiss hw ((hfr w (hJK hw)).mpr (frontier_interior_subset hz))
    exact fun z hz => hc.m76_subset_of_disjoint_frontier isOpen_interior hd
      ⟨g m, mem_image_of_mem _ hmJ, hmR⟩ (mem_image_of_mem _ hz)
  have hJreg : J.space = ((M reg).barycentricDualBlock s).space := by
    rw [← K.barycentricDualBlock_space_inter_subcomplex (M reg) (hMK reg) s]
    exact (inter_eq_left.mpr (fun z hz => (hreg z (hJK hz)).mpr (interior_subset (hJR hz)))).symm
  have hlink (v : E) (hvs : v ∈ s) :
      J.space ⊆ ((K.barycentricDualBlock {v}).link v).space := by
    have hvK := K.face_subset_vertices hsK hvs
    have hstrict : ({v} : Finset E) ⊂ s :=
      (Finset.singleton_subset_iff.mpr hvs).ssubset_of_ne (by
        intro he
        rw [← he] at hcard
        simp at hcard)
    simpa only [Finset.centroid_singleton, id_eq] using
      space_subset_of_le (K.barycentricDualBlock_le_link_of_ssubset hvK hstrict)
  have hJstar : J.space ⊆ (K.closedStar p0).space := by
    intro z hz
    have hV := space_subset_of_le (K.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr hps)) hz
    obtain ⟨v, hv, hzv⟩ := mem_space_iff.mp hV
    obtain ⟨t, ht, hvt⟩ := K.exists_original_star_face_of_vertex_dual_face hpK hv
    exact (K.closedStar p0).convexHull_subset_space ht (hvt hzv)
  have hsubstar (j : κ) : (M j).closedStar p0 ≤ K.closedStar p0 :=
    fun _ hv => ⟨hMK j hv.1, hMK j hv.2⟩
  have hsmallstar (j : κ) : (M j).closedStar p0 ≤ M j := fun _ hv => hv.1
  have hstarzero (z : E) (hz : z ∈ ((M arc).closedStar p0).space) :
      B p (g z) 0 = 0 ∧ B p (g z) 1 = 0 := by
    have hzK := space_subset_of_le (hsubstar arc) hz
    exact ((haxis (g z) (hsource hzK)).mp
      ((harc z (hstarK hzK)).mp (space_subset_of_le (hsmallstar arc) hz))).2
  have hstarinj : InjOn (fun z => B p (g z)) (K.closedStar p0).space :=
    (K.exists_original_open_neighborhood_inside_closedStar (Set.toFinite K.faces)
      H g hg hpK (hAC hpA) (B p) hsource).1
  have hArcFace : ((M arc).closedStar p0).AffineOnFaces (fun z => B p (g z) 2) := by
    change ((M arc).closedStar p0).AffineOnFaces
      (((ContinuousLinearMap.proj (2 : Fin 3) : V3 →L[ℝ] ℝ).toContinuousAffineMap) ∘
        fun z => B p (g z))
    exact (show ((M arc).closedStar p0).AffineOnFaces (fun z => B p (g z)) from
      fun v hv => hface v (hsubstar arc hv)).postcomp _
  have hArcInj : InjOn (fun z => B p (g z) 2) ((M arc).closedStar p0).space := by
    intro x hx y hy he
    apply hstarinj (space_subset_of_le (hsubstar arc) hx) (space_subset_of_le (hsubstar arc) hy)
    ext j
    fin_cases j
    · exact (hstarzero x hx).1.trans (hstarzero y hy).1.symm
    · exact (hstarzero x hx).2.trans (hstarzero y hy).2.symm
    · exact he
  have hmax (v : Finset E) (hv : v ∈ (M arc).faces) (hsv : s ⊆ v) : v = s := by
    have hvstar : v ∈ ((M arc).closedStar p0).faces :=
      ⟨hv, by simpa only [Finset.insert_eq_of_mem (hsv hps)] using hv⟩
    have hbound := hArcFace.face_card_le_of_injOn hArcInj hvstar
    exact (Finset.eq_of_subset_of_card_le hsv (by simpa [hcard] using hbound)).symm
  have hJarc : J.space ∩ (M arc).space = {m} :=
    (K.barycentricDualBlock_space_inter_subcomplex (M arc) (hMK arc) s).trans
      ((M arc).barycentricDualBlock_space_eq_singleton_of_maximal hs hmax)
  let f : E → V3 := fun z => B p (g z) - B p (g p0)
  have hcoord (z : E) (i : Fin 2) : f z i.castSucc = B p (g z) i.castSucc := by
    fin_cases i <;> simp [f, hpzero.1, hpzero.2]
  have hpSi (i : Fin 2) : p0 ∈ (M (sheet i)).vertices := by
    apply hvertex (sheet i) hpK
    apply (hsheet i p0 (K.vertices_subset_space hpK)).mpr
    apply (hsheets i (g p0) (hsource hpstar)).mpr
    refine ⟨hAR hpA, ?_⟩
    fin_cases i
    · exact hpzero.1
    · exact hpzero.2
  have hsSi (i : Fin 2) : s ∈ (M (sheet i)).faces := by
    apply hfull (sheet i) s hsK
    intro z hzs
    have hzstar : z ∈ ((M arc).closedStar p0).space := by
      apply ((M arc).closedStar p0).subset_space
        (show s ∈ ((M arc).closedStar p0).faces from
          ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩) hzs
    have hzK := space_subset_of_le (hsubstar arc) hzstar
    apply hvertex (sheet i) (K.face_subset_vertices hsK hzs)
    apply (hsheet i z (hstarK hzK)).mpr
    apply (hsheets i (g z) (hsource hzK)).mpr
    refine ⟨hAR ((harc z (hstarK hzK)).mp ((M arc).subset_space hs hzs)), ?_⟩
    fin_cases i
    · exact (hstarzero z hzstar).1
    · exact (hstarzero z hzstar).2
  have hsheetdata (i : Fin 2) : ∃ t u : Finset E,
      t ∈ (M (sheet i)).faces ∧ u ∈ (M (sheet i)).faces ∧ s ⊆ t ∧ s ⊆ u ∧
      t.card = 3 ∧ u.card = 3 ∧ t ≠ u ∧
      (∀ v ∈ (M (sheet i)).faces, s ⊆ v → v.card = 3 → v = t ∨ v = u) ∧
      IsFinitePLBallPair ℝ ((M (sheet i)).barycentricDualBlock s).space
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      m ∈ ((M (sheet i)).barycentricDualBlock s).space \ {t.centroid ℝ id, u.centroid ℝ id} ∧
      (((M (sheet i)).barycentricDualBlock s).link m).space = {t.centroid ℝ id, u.centroid ℝ id} ∧
      B p (g (t.centroid ℝ id)) i.rev.castSucc < 0 ∧
      0 < B p (g (u.centroid ℝ id)) i.rev.castSucc := by
    let N := (M (sheet i)).closedStar p0
    let r : V3 →ᴬ[ℝ] P2 := ((ContinuousLinearMap.proj i.rev.castSucc).prod
      (ContinuousLinearMap.proj (2 : Fin 3))).toContinuousAffineMap
    let a : P2 →ᴬ[ℝ] V3 := (ContinuousLinearMap.pi fun j : Fin 3 =>
      if j = i.castSucc then 0 else
        if j = i.rev.castSucc then ContinuousLinearMap.fst ℝ ℝ ℝ
        else ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
    let ell : E → P2 := fun z => r (f z)
    have hra (w : P2) : r (a w) = w := by fin_cases i <;> simp [r, a]
    have ha0 : a 0 = 0 := by ext j; fin_cases i <;> fin_cases j <;> simp [a]
    have haz (w : P2) : a w i.castSucc = 0 := by fin_cases i <;> simp [a]
    have hNz (z : E) (hz : z ∈ N.space) : f z i.castSucc = 0 := by
      rw [hcoord]
      have hzK := space_subset_of_le (hsubstar (sheet i)) hz
      exact ((hsheets i (g z) (hsource hzK)).mp ((hsheet i z (hstarK hzK)).mp
        (space_subset_of_le (hsmallstar (sheet i)) hz))).2
    let shift : V3 →ᴬ[ℝ] V3 := ContinuousAffineMap.id ℝ V3 -
      ContinuousAffineMap.const ℝ V3 (B p (g p0))
    have hell : N.AffineOnFaces ell :=
      ((show N.AffineOnFaces (fun z => B p (g z)) from
        fun v hv => hface v (hsubstar (sheet i) hv)).postcomp shift).postcomp r
    have hfi : InjOn f (K.closedStar p0).space := by
      intro x hx y hy he
      apply hstarinj hx hy
      simpa only [f, sub_add_cancel] using congrArg (fun v : V3 => v + B p (g p0)) he
    have helli : InjOn ell N.space := by
      intro x hx y hy he
      apply hfi (space_subset_of_le (hsubstar (sheet i)) hx)
        (space_subset_of_le (hsubstar (sheet i)) hy)
      have hf0 := congrArg Prod.fst he
      have hf1 := congrArg Prod.snd he
      ext j
      fin_cases i <;> fin_cases j
      · exact (hNz x hx).trans (hNz y hy).symm
      · exact hf0
      · exact hf1
      · exact hf0
      · exact (hNz x hx).trans (hNz y hy).symm
      · exact hf1
    obtain ⟨eta, heta, hsmall⟩ := (M (sheet i)).exists_ball_inter_space_subset_closedStar
      (Set.toFinite _) (hpSi i)
    let O : Set X := ((B p).source ∩ interior C) ∩ interior R ∩ F ⁻¹' ball p0 eta
    have hOo : IsOpen O := (((B p).open_source.inter isOpen_interior).inter
      isOpen_interior).inter (isOpen_ball.preimage hF)
    have hOB : O ⊆ (B p).source := fun _ hx => hx.1.1.1
    have hpO : (g p0 : X) ∈ O := by
      refine ⟨⟨⟨hsource hpstar, hAC hpA⟩, hpR⟩, ?_⟩
      change F (g p0) ∈ ball p0 eta
      rw [hFg p0 (K.vertices_subset_space hpK)]
      exact mem_ball_self heta
    let b : X → V3 := fun x => B p x - B p (g p0)
    have hbO : IsOpen (b '' O) := by
      have he : b '' O = (Homeomorph.subRight (B p (g p0))) '' ((B p) '' O) := by
        rw [image_image]; rfl
      rw [he]
      exact (Homeomorph.subRight _).isOpenMap _ ((B p).isOpen_image_of_subset_source hOo hOB)
    let W := a ⁻¹' (b '' O)
    have hWo : IsOpen W := hbO.preimage a.continuous
    have hW0 : (0 : P2) ∈ W := ⟨g p0, hpO, by simp [b, ha0]⟩
    have hWimage : W ⊆ ell '' N.space := by
      rintro w ⟨x, hx, hbx⟩
      have hxC : x ∈ C := interior_subset hx.1.1.2
      have hxR : x ∈ R := interior_subset hx.1.2
      have hxzero : B p x i.castSucc = 0 := by
        have he := congrArg (fun v : V3 => v i.castSucc) hbx
        have hpz : B p (g p0) i.castSucc = 0 := by
          fin_cases i
          · exact hpzero.1
          · exact hpzero.2
        simpa only [b, Pi.sub_apply, hpz, sub_zero, haz] using he
      have hxS := (hsheets i x (hOB hx)).mpr ⟨hxR, hxzero⟩
      have hFxS : F x ∈ (M (sheet i)).space :=
        (hsheet i (F x) (hFK x hxC)).mpr ((hgF x hxC).symm ▸ hxS)
      refine ⟨F x, hsmall ⟨hFxS, hx.2⟩, ?_⟩
      change r (B p (g (F x)) - B p (g p0)) = w
      rw [hgF x hxC]
      change r (b x) = w
      rw [hbx, hra]
    have hellp : ell p0 = 0 := by simp [ell, f, r]
    have hellint : ell p0 ∈ interior (ell '' N.space) := by
      rw [hellp]
      exact interior_maximal hWimage hWo hW0
    obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, hco, hI, hmI, hbI⟩ :=
      (M (sheet i)).exists_dual_interval_of_embedded_star (hsSi i)
        (by simpa using hcard) hps ell hell helli hellint
    have htN : t ∈ N.faces := ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hps)] using ht⟩
    have huN : u ∈ N.faces := ⟨hu, by simpa only [Finset.insert_eq_of_mem (hsu hps)] using hu⟩
    have hsN : s ∈ N.faces := ⟨hsSi i, by simpa only [Finset.insert_eq_of_mem hps] using hsSi i⟩
    have hsign := hell.opposite_centroid_signs helli hsN htN huN
      (by simpa using hcard) htc huc hst hsu htu (LinearMap.fst ℝ ℝ ℝ).toAffineMap
      (by intro hz; have h := congrArg (fun L : P2 →ₗ[ℝ] ℝ => L (1, 0)) hz; norm_num at h)
      (by
        intro z hzs
        have hzstar : z ∈ ((M arc).closedStar p0).space :=
          ((M arc).closedStar p0).subset_space
            ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩ hzs
        change f z i.rev.castSucc = 0
        rw [hcoord]
        fin_cases i
        · exact (hstarzero z hzstar).2
        · exact (hstarzero z hzstar).1)
    change (f (t.centroid ℝ id) i.rev.castSucc < 0 ∧ 0 < f (u.centroid ℝ id) i.rev.castSucc) ∨
      (0 < f (t.centroid ℝ id) i.rev.castSucc ∧ f (u.centroid ℝ id) i.rev.castSucc < 0) at hsign
    simp only [hcoord] at hsign
    rcases hsign with hsg | hsg
    · exact ⟨t, u, ht, hu, hst, hsu, by simpa using htc, by simpa using huc,
        htu, by simpa using hco, hI, hmI, hbI, hsg⟩
    · refine ⟨u, t, hu, ht, hsu, hst, by simpa using huc, by simpa using htc,
        htu.symm, ?_, ?_, ?_, ?_, hsg.2, hsg.1⟩
      · intro v hv hsv hvc
        exact (hco v hv hsv (by simpa using hvc)).symm
      · simpa only [pair_comm] using hI
      · simpa only [pair_comm] using hmI
      · simpa only [pair_comm] using hbI
  choose t u ht using hsheetdata
  refine ⟨p, hps, hpR, hJball, hJR, hJreg, hmiss, hJarc, hlink, t, u, ?_⟩
  intro i
  obtain ⟨htf, huf, hst, hsu, htc, huc, htu, hco, hI, hmI, hbI, hneg, hpos⟩ := ht i
  let I := (M (sheet i)).barycentricDualBlock s
  have hIs : I.space = J.space ∩ (M (sheet i)).space :=
    (K.barycentricDualBlock_space_inter_subcomplex (M (sheet i)) (hMK (sheet i)) s).symm
  have hIq : I.space ∩ q = {(t i).centroid ℝ id, (u i).centroid ℝ id} := by
    rw [← J.link_space_eq_inter_of_closedStar_eq I
      (K.barycentricDualBlock_mono_of_subcomplex (M (sheet i)) (hMK (sheet i)) s) m
      ((M (sheet i)).barycentricDualBlock_closedStar_faceCentroid (hsSi i))]
    exact hbI
  have hzero : J.space ∩ {z | B p (g z) i.castSucc = 0} = I.space := by
    rw [hIs]
    ext z
    constructor
    · rintro ⟨hz, hzi⟩
      exact ⟨hz, (hsheet i z (hJK hz)).mpr
        ((hsheets i (g z) (hsource (hJstar hz))).mpr ⟨interior_subset (hJR hz), hzi⟩)⟩
    · rintro ⟨hz, hzi⟩
      exact ⟨hz, ((hsheets i (g z) (hsource (hJstar hz))).mp
        ((hsheet i z (hJK hz)).mp hzi)).2⟩
  have hqzero : q ∩ {z | B p (g z) i.castSucc = 0} =
      {(t i).centroid ℝ id, (u i).centroid ℝ id} := by
    rw [← hIq, ← hzero]
    ext z
    exact ⟨fun h => ⟨⟨hJball.1 h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  exact ⟨htf, huf, hst, hsu, htc, huc, htu, hco, hIs, hI, hmI, hIq, hzero,
    hqzero, hneg, hpos⟩

end PoincareConjecture.M76.Dehn
