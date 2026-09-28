import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcRemainderMesh
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoCornerCoreMatching
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcRadialContacts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoBandChainCompatibility
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MatchedRegionParentsRetained
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapCompatibility

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

private theorem two_arc_band_lower_subset
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} {r : Bool → ℝ} (rev : Bool)
    {n : ℕ} (c : Fin (n + 1) → ℝ) (hc : StrictMono c)
    (hfirst : c 0 = r (if rev then !false else false))
    (hlast : c (Fin.last n) = T - r (if rev then !true else true)) (i : Fin n) :
    (fun t => gamma (if rev then T - t else t)) '' Icc (c i.castSucc) (c i.succ) ⊆
      gamma '' Icc (r false) (T - r true) := by
  rintro p ⟨t, ht, rfl⟩
  have hlo : r (if rev then !false else false) ≤ t := by
    rw [← hfirst]
    exact (hc.monotone (Fin.zero_le i.castSucc)).trans ht.1
  have hhi : t ≤ T - r (if rev then !true else true) := by
    rw [← hlast]
    exact ht.2.trans (hc.monotone (Fin.le_last i.succ))
  refine ⟨if rev then T - t else t, ?_, rfl⟩
  cases rev with
  | false => simpa using And.intro hlo hhi
  | true =>
    have hlo' : r true ≤ t := by simpa using hlo
    have hhi' : t ≤ T - r false := by simpa using hhi
    change T - t ∈ Icc (r false) (T - r true)
    constructor <;> linarith

theorem m64Intrinsic_exists_two_arc_region_coordinate_parents
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hareg : ∀ t ∈ Ioo (0 : ℝ) A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo (0 : ℝ) B, deriv beta t ≠ 0)
    (hinter : (alpha '' Icc 0 A) ∩ (beta '' Icc 0 B) ⊆ {alpha 0, alpha A})
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hind0 : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U) (hcompact : IsCompact (closure U)) :
    ∃ (m : ℕ) (C : Fin m → OpenPartialHomeomorph Plane AnnulusCoordinates)
      (b : Fin m → AffineBasis (Fin 3) ℝ Plane) (p0 p1 : Fin m),
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p) (C p).source) ∧
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p).symm (C p).target) ∧
      (∀ p, convexHull ℝ (range (b p)) ⊆ (C p).source) ∧
      (∀ p q, p ≠ q → CoordinateTriangleBoundaryIntersection (C p) (C q) (b p) (b q)) ∧
      (⋃ p, C p '' convexHull ℝ (range (b p))) = closure U ∧
      C p0 (b p0 0) = alpha 0 ∧ C p1 (b p1 0) = alpha A := by
  classical
  obtain ⟨H, r, F, W, positive, hdata, hCCorners,
    rev0, d0, n0, c0, L0, G0, f0, ell0, _, hc0, hfirst0, hlast0, _,
    B0, hB0, hsep0, hadj0, hcap0, _,
    rev1, d1, n1, c1, L1, G1, f1, ell1, _, hc1, hfirst1, hlast1, _,
    B1, hB1, hsep1, hadj1, hcap1, _, hcross, core, hcore, hrecovery, hlocal⟩ :=
    m64Intrinsic_exists_two_arc_remainder_mesh ha hb hA hB hai hbi hareg hbreg
      hinter hbase hend hind0 hind1 hU hV hdisj hfU hfV hcompact
  let occupied (e : Bool) (i : Bool × Bool) :=
    if positive e then i = (true, true) else i ≠ (true, true)
  let D (e : Bool) := ⋃ i, ⋃ (_ : occupied e i),
    F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
  let R := ((D false ∪ D true) ∪ ⋃ i, (B0 i).carrier) ∪ ⋃ i, (B1 i).carrier
  change Disjoint (D false) (D true) at hCCorners
  change core.toPlaneComplex.support = closure (U \ R) at hcore
  change closure U = R ∪ core.toPlaneComplex.support at hrecovery
  change ∀ p ∈ closure U ∩ frontier U, ∃ Q : Set AnnulusCoordinates,
    IsOpen Q ∧ p ∈ Q ∧ Q ∩ closure U ⊆ R at hlocal
  have hr (e : Bool) := (hdata e).1
  have hrbound (e : Bool) := (hdata e).2.1
  have hH0 (e : Bool) := (hdata e).2.2.2.1
  have haxis (e : Bool) := (hdata e).2.2.2.2.2.2.1
  have haxis' (e : Bool) := (hdata e).2.2.2.2.2.2.2.1
  have hsmall (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.1
  have hFD (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.2.2.2.1
  have hrA (e : Bool) : r e ≤ A := by linarith [hrbound e, min_le_left A B]
  have hrB (e : Bool) : r e ≤ B := by linarith [hrbound e, min_le_right A B]
  choose face hface hzero hone htwo Q b hQ hQi hsource hcarrier hboundary using
    fun (e : Bool) (i : Bool × Bool) => m64Intrinsic_exists_coordinate_face_of_chosen_cap
      (F e i) (hr e) (hFD e i).1 (hFD e i).2.2.1 (hFD e i).2.2.2.1
  have hfaceunion (e : Bool) : (⋃ i, ⋃ (_ : occupied e i), (face e i).carrier) = D e := by
    simp only [hface]
    rfl
  have hfaceD (e : Bool) (i : Bool × Bool) (hi : occupied e i) :
      (face e i).carrier ⊆ D e := by
    rw [← hfaceunion e]
    exact fun _ hx => mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hx⟩⟩
  have hDall (e : Bool) : D e ⊆ D false ∪ D true := by
    cases e
    · exact subset_union_left
    · exact subset_union_right
  have hsector (e : Bool) (i : Bool × Bool) : (face e i).carrier ⊆
      H e '' ((H e).source ∩ (sectorParameterEquiv 0 i) ''
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
    rw [hface]
    exact (hFD e i).2.2.2.2.2.2.2.1
  have hsecond (e : Bool) (i : Bool × Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ((face e i).boundary 1).map t = H e (sectorParameterEquiv 0 i (0, t * r e)) := by
    rw [hone]
    exact (hFD e i).2.2.2.2.2.1 _ ⟨mul_nonneg ht.1 (hr e).le,
      mul_le_of_le_one_left (hr e).le ht.2⟩
  have hfirstedge (e : Bool) (i : Bool × Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ((face e i).boundary 2).map t = H e (sectorParameterEquiv 0 i (t * r e, 0)) := by
    rw [htwo]
    exact (hFD e i).2.2.2.2.1 _ ⟨mul_nonneg ht.1 (hr e).le,
      mul_le_of_le_one_left (hr e).le ht.2⟩
  have hchord (e : Bool) (i : Bool × Bool) (t : ℝ) : ((face e i).boundary 0).map t =
      (1 - t) • H e (sectorParameterEquiv 0 i (r e, 0)) +
        t • H e (sectorParameterEquiv 0 i (0, r e)) := by
    rw [hzero, (hFD e i).2.2.2.2.2.2.1,
      (hFD e i).2.2.2.2.1 (r e) ⟨(hr e).le, le_rfl⟩,
      (hFD e i).2.2.2.2.2.1 (r e) ⟨(hr e).le, le_rfl⟩]
  have hCC (e : Bool) := m64Intrinsic_retained_caps_canonical_compatibility
    (H e) (hr e) (face e) (Q e) (b e) (hcarrier e) (hboundary e) (hsector e)
      (fun i => by rw [hface]; exact (hFD e i).2.2.2.2.2.2.2.2)
      (hsmall e) (hsecond e) (hfirstedge e)
  let I := Fin n0 ⊕ Fin n1
  let L : I → AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates := Sum.elim
    (fun i => collarParameterEquiv.trans (L0 i).symm)
    (fun i => collarParameterEquiv.trans (L1 i).symm)
  let lo : I → ℝ → ℝ := Sum.elim f0 f1
  let a : I → ℝ := Sum.elim (fun i => G0 i (c0 i.castSucc)) (fun i => G1 i (c1 i.castSucc))
  let z : I → ℝ := Sum.elim (fun i => G0 i (c0 i.succ)) (fun i => G1 i (c1 i.succ))
  let ua : I → ℝ := Sum.elim
    (fun i => (L0 i (d0 (c0 i.castSucc))).1) (fun i => (L1 i (d1 (c1 i.castSucc))).1)
  let wa : I → ℝ := Sum.elim
    (fun i => (L0 i (d0 (c0 i.castSucc))).2) (fun i => (L1 i (d1 (c1 i.castSucc))).2)
  let ub : I → ℝ := Sum.elim
    (fun i => (L0 i (d0 (c0 i.succ))).1) (fun i => (L1 i (d1 (c1 i.succ))).1)
  let wb : I → ℝ := Sum.elim
    (fun i => (L0 i (d0 (c0 i.succ))).2) (fun i => (L1 i (d1 (c1 i.succ))).2)
  let ell : I → ℝ := Sum.elim (fun _ => ell0) (fun _ => ell1)
  let Bands : ∀ i, ObliqueBandFaces (L i).toHomeomorph.toOpenPartialHomeomorph
      (lo i) (a i) (z i) (ua i) (wa i) (ub i) (wb i) (ell i) (ell i) := Sum.rec B0 B1
  let g0 : ℝ → AnnulusCoordinates := fun t => alpha (if rev0 then A - t else t)
  let g1 : ℝ → AnnulusCoordinates := fun t => beta (if rev1 then B - t else t)
  let cut0 (j : Fin (n0 + 1)) := segment ℝ (g0 (c0 j)) (g0 (c0 j) + ell0 • d0 (c0 j))
  let cut1 (j : Fin (n1 + 1)) := segment ℝ (g1 (c1 j)) (g1 (c1 j) + ell1 • d1 (c1 j))
  have hBB := m64Intrinsic_two_band_chains_faces_canonical
    (fun i => (L i).toHomeomorph.toOpenPartialHomeomorph) lo a z ua wa ub wb ell ell Bands
      cut0 (fun i => (hB0 i).2.1) (fun i => (hB0 i).2.2.1) hsep0 hadj0
      cut1 (fun i => (hB1 i).2.1) (fun i => (hB1 i).2.2.1) hsep1 hadj1 hcross
  have htrim0 (i : Fin n0) : (B0 i).lowerArc ⊆ alpha '' Icc (r false) (A - r true) := by
    rw [(hB0 i).1]
    exact two_arc_band_lower_subset rev0 c0 hc0 hfirst0 hlast0 i
  have htrim1 (i : Fin n1) : (B1 i).lowerArc ⊆ beta '' Icc (r false) (B - r true) := by
    rw [(hB1 i).1]
    exact two_arc_band_lower_subset rev1 c1 hc1 hfirst1 hlast1 i
  have hlower (i : I) : (Bands i).lowerArc ⊆ frontier U := by
    rw [hfU]
    cases i with
    | inl i => exact (htrim0 i).trans ((image_mono (Icc_subset_Icc (hr false).le
        (sub_le_self A (hr true).le))).trans subset_union_left)
    | inr i => exact (htrim1 i).trans ((image_mono (Icc_subset_Icc (hr false).le
        (sub_le_self B (hr true).le))).trans subset_union_right)
  have hbandremove (i : I) : (Bands i).carrier ⊆ R := by
    cases i with
    | inl i => exact fun _ hx => Or.inl (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
    | inr i => exact fun _ hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
  have hbandregion (i : I) : (Bands i).carrier \ (Bands i).lowerArc ⊆ U := by
    cases i with
    | inl i => exact (hB0 i).2.2.2.2
    | inr i => exact (hB1 i).2.2.2.2
  have hcuts (i : I) (right : Bool) : ∃ u v : AnnulusCoordinates,
      ((Bands i).endpointEdge right).map '' Icc (0 : ℝ) 1 = segment ℝ u v := by
    rw [(Bands i).endpointEdge_image]
    cases i with
    | inl i =>
      cases right
      · exact ⟨_, _, (hB0 i).2.1⟩
      · exact ⟨_, _, (hB0 i).2.2.1⟩
    | inr i =>
      cases right
      · exact ⟨_, _, (hB1 i).2.1⟩
      · exact ⟨_, _, (hB1 i).2.2.1⟩
  let axes (e : Bool) := (fun t : ℝ => H e (0, t * r e)) '' Icc 0 1 ∪
    (fun t : ℝ => H e (t * r e, 0)) '' Icc 0 1
  have haxes (e : Bool) : axes e ⊆ frontier U := by
    rw [hfU]
    rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · dsimp only
      rw [haxis']
      refine Or.inr ⟨_, ?_, rfl⟩
      have hs : t * r e ∈ Icc (0 : ℝ) (r e) :=
        ⟨mul_nonneg ht.1 (hr e).le, mul_le_of_le_one_left (hr e).le ht.2⟩
      cases e <;> dsimp at hs ⊢ <;> constructor <;>
        linarith [hs.1, hs.2, hrB false, hrB true]
    · dsimp only
      rw [haxis]
      refine Or.inl ⟨_, ?_, rfl⟩
      have hs : t * r e ∈ Icc (0 : ℝ) (r e) :=
        ⟨mul_nonneg ht.1 (hr e).le, mul_le_of_le_one_left (hr e).le ht.2⟩
      cases e <;> dsimp at hs ⊢ <;> constructor <;>
        linarith [hs.1, hs.2, hrA false, hrA true]
  have hcapremove (e : Bool) :
      (⋃ i, ⋃ (_ : occupied e i), (face e i).carrier) ⊆ R := by
    rw [hfaceunion]
    exact (hDall e).trans (subset_union_left.trans subset_union_left)
  obtain ⟨mesh, hmesh, _, hmeshcap, hmeshband⟩ :=
    m64Intrinsic_refine_core_to_two_corners_and_bands H r face positive Q b hQ hQi
      hsource hcarrier hboundary hsector hsecond hfirstedge hchord
      L lo a z ua wa ub wb ell ell Bands haxes hcapremove hbandremove hlower hlocal core hcore
  have houter (i : I) (e : Bool) :
      D e ∩ (Bands i).carrier ⊆ (Bands i).leftCut ∪ (Bands i).rightCut := by
    have ht : (D false ∪ D true) ∩ (Bands i).carrier ⊆
        (Bands i).leftCut ∪ (Bands i).rightCut := by
      cases i with
      | inl i =>
        change (D false ∪ D true) ∩ (B0 i).carrier ⊆ (B0 i).leftCut ∪ (B0 i).rightCut
        rw [hcap0 i]
        split_ifs <;> simp
      | inr i =>
        change (D false ∪ D true) ∩ (B1 i).carrier ⊆ (B1 i).leftCut ∪ (B1 i).rightCut
        rw [hcap1 i]
        split_ifs <;> simp
    exact fun _ hx => ht ⟨hDall e hx.1, hx.2⟩
  have havoid0 := m64Intrinsic_two_arc_interior_disjoint hai hinter
  have havoid1 : Disjoint (beta '' Ioo 0 B) (alpha '' Icc 0 A) := by
    apply m64Intrinsic_two_arc_interior_disjoint hbi
    simpa only [inter_comm, hbase, hend] using hinter
  have htips (i : I) (e : Bool) :
      axes e ∩ (Bands i).lowerArc ⊆ {H e (r e, 0), H e (0, r e)} := by
    cases i with
    | inl i =>
      exact fun _ hx => m64Intrinsic_corner_axes_inter_trimmed_arc_subset_tips
        hai havoid0 r hr hrA hrB e (H e) (haxis e) (haxis' e) ⟨hx.1, htrim0 i hx.2⟩
    | inr i =>
      exact fun _ hx => m64Intrinsic_corner_axes_inter_other_trimmed_arc_subset_tips
        hbi havoid1 r hr hrA hrB e (H e) (haxis e) (haxis' e) ⟨hx.1, htrim1 i hx.2⟩
  have hcoordinates (e : Bool) (i : Bool × Bool) :
      ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
        (basis : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
        convexHull ℝ (range basis) ⊆ C.source ∧
        (face e i).carrier = C '' convexHull ℝ (range basis) ∧
        ∀ k, ((face e i).boundary k).map = C ∘
          affineChartSegment (basis (k.succAbove 0)) (basis (k.succAbove 1)) :=
    ⟨Q e i, b e i, hQ e i, hQi e i, hsource e i, hcarrier e i, hboundary e i⟩
  have hownchord (i : I) (e : Bool) (j : Bool × Bool) (hj : occupied e j) :
      (face e j).carrier ∩ (Bands i).carrier ⊆
        ((face e j).boundary 0).map '' Icc (0 : ℝ) 1 := by
    apply m64Intrinsic_retained_corner_band_inter_subset_chord (H e) (hr e)
      (face e) (positive e) ?_ (hsector e) (hsecond e) (hfirstedge e) (hchord e)
      (hcoordinates e) (Bands i) (disjoint_frontier_iff_isOpen.mpr hU).symm
      (hbandregion i) (haxes e) (htips i e) ?_ j hj
    · simpa [sectorParameterEquiv_apply] using hsmall e (true, true) (r e) ⟨(hr e).le, le_rfl⟩
    · change (⋃ j, ⋃ (_ : occupied e j), (face e j).carrier) ∩ (Bands i).carrier ⊆ _
      rw [hfaceunion]
      exact houter i e
  let J := {p : Bool × (Bool × Bool) // occupied p.1 p.2}
  let G : J → OpenPartialHomeomorph Plane AnnulusCoordinates := fun j => Q j.1.1 j.1.2
  let d : J → AffineBasis (Fin 3) ℝ Plane := fun j => b j.1.1 j.1.2
  have hGG (j k : J) (hjk : j ≠ k) :
      CoordinateTriangleBoundaryIntersection (G j) (G k) (d j) (d k) := by
    rcases j with ⟨⟨e, i⟩, hi⟩
    rcases k with ⟨⟨f, j⟩, hj⟩
    by_cases hef : e = f
    · subst f
      exact hCC e i j (fun h => hjk (Subtype.ext (congrArg (Prod.mk e) h)))
    · apply CoordinateTriangleBoundaryIntersection.disjoint
      change Disjoint (Q e i '' convexHull ℝ (range (b e i)))
        (Q f j '' convexHull ℝ (range (b f j)))
      rw [← hcarrier, ← hcarrier]
      have hDD : Disjoint (D e) (D f) := by
        cases e <;> cases f
        · exact False.elim (hef rfl)
        · exact hCCorners
        · exact hCCorners.symm
        · exact False.elim (hef rfl)
      exact hDD.mono (hfaceD e i hi) (hfaceD f j hj)
  have hchordimage (j : J) : G j '' affineSegment ℝ (d j ((0 : Fin 3).succAbove 0))
      (d j ((0 : Fin 3).succAbove 1)) = segment ℝ
        (H j.1.1 (sectorParameterEquiv 0 j.1.2 (r j.1.1, 0)))
        (H j.1.1 (sectorParameterEquiv 0 j.1.2 (0, r j.1.1))) := by
    dsimp only [G, d]
    rw [← Euler.affineChartSegment_image, ← image_comp, ← hboundary, segment_eq_image]
    exact image_congr (fun t _ => hchord j.1.1 j.1.2 t)
  obtain ⟨m, C, bases, hC, hCi, hCs, hCp, hCsupport, hkeep⟩ :=
    m64Intrinsic_exists_cap_band_core_coordinate_parents_retaining_caps
      (fun i => (L i).toHomeomorph.toOpenPartialHomeomorph) lo a z ua wa ub wb ell ell Bands
      (fun i => contMDiffOn_iff_contDiffOn.mpr (L i).contDiff.contDiffOn)
      (fun i => contMDiffOn_iff_contDiffOn.mpr (L i).symm.contDiff.contDiffOn)
      hBB hcuts G d (fun j => hQ j.1.1 j.1.2) (fun j => hQi j.1.1 j.1.2)
      (fun j => hsource j.1.1 j.1.2) hGG (fun _ => 0)
      (fun j => H j.1.1 (sectorParameterEquiv 0 j.1.2 (r j.1.1, 0)))
      (fun j => H j.1.1 (sectorParameterEquiv 0 j.1.2 (0, r j.1.1))) hchordimage
      (by
        intro i j p hp
        change p ∈ (Bands i).carrier ∩ (Q j.1.1 j.1.2 '' convexHull ℝ (range (b j.1.1 j.1.2))) at hp
        rw [← hcarrier] at hp
        exact houter i j.1.1 ⟨hfaceD _ _ j.2 hp.2, hp.1⟩)
      (by
        intro i j p hp
        change p ∈ Q j.1.1 j.1.2 '' affineSegment ℝ
          (b j.1.1 j.1.2 ((0 : Fin 3).succAbove 0)) (b j.1.1 j.1.2 ((0 : Fin 3).succAbove 1))
        rw [← Euler.affineChartSegment_image, ← image_comp, ← hboundary]
        exact hownchord i j.1.1 j.1.2 j.2 ⟨(hcarrier _ _).symm ▸ hp.2, hp.1⟩)
      mesh (fun t j => hmeshcap j.1.1 j.1.2 j.2 t) (fun t i p => hmeshband i t p)
  have hchosen : (⋃ j : J, G j '' convexHull ℝ (range (d j))) = D false ∪ D true := by
    ext p
    constructor
    · intro hp
      obtain ⟨j, hp⟩ := mem_iUnion.mp hp
      exact hDall j.1.1 (hfaceD _ _ j.2 ((hcarrier _ _).symm ▸ hp))
    · rintro (hp | hp)
      · obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
        apply mem_iUnion.mpr
        refine ⟨⟨(false, i), hi⟩, ?_⟩
        change p ∈ Q false i '' convexHull ℝ (range (b false i))
        rwa [← hcarrier, hface]
      · obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
        apply mem_iUnion.mpr
        refine ⟨⟨(true, i), hi⟩, ?_⟩
        change p ∈ Q true i '' convexHull ℝ (range (b true i))
        rwa [← hcarrier, hface]
  have hbands : (⋃ i : I, (Bands i).carrier) =
      (⋃ i, (B0 i).carrier) ∪ ⋃ i, (B1 i).carrier := by
    simp only [I, Bands, iUnion_sum]
  have htip (e : Bool) (i : Bool × Bool) : Q e i (b e i 0) = alpha (if e then A else 0) := by
    have hb0 := congrFun (hboundary e i 1) 0
    have hstart : ((face e i).boundary 1).map 0 = Q e i (b e i 0) := by
      simpa [Function.comp_apply, affineChartSegment] using hb0
    rw [← hstart, hsecond e i 0 (by simp)]
    refine (congrArg (H e) ?_).trans (hH0 e)
    ext <;> simp [sectorParameterEquiv_apply]
  let selected (e : Bool) : Bool × Bool := if positive e then (true, true) else (false, false)
  have hselected (e : Bool) : occupied e (selected e) := by
    dsimp only [occupied, selected]
    split_ifs <;> simp
  obtain ⟨p0, hp0C, hp0b⟩ := hkeep ⟨(false, selected false), hselected false⟩
  obtain ⟨p1, hp1C, hp1b⟩ := hkeep ⟨(true, selected true), hselected true⟩
  refine ⟨m, C, bases, p0, p1, hC, hCi, hCs, hCp, ?_, ?_, ?_⟩
  · rw [hCsupport, hchosen, hbands, hmesh]
    simpa only [R, union_assoc] using hrecovery.symm
  · rw [hp0C, hp0b]
    exact htip false (selected false)
  · rw [hp1C, hp1b]
    exact htip true (selected true)

end PoincareConjecture
