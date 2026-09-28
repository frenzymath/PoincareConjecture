import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MatchedRegionParents
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapCompatibility
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapBandChords











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_exists_return_region_coordinate_parents
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) (hcompact : IsCompact (closure U))
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • Poincare.Topology.Plane.Curves.quarterTurn (deriv gamma t) ∈ U) :
    ∃ (m : ℕ) (C : Fin m → OpenPartialHomeomorph Plane AnnulusCoordinates)
      (b : Fin m → AffineBasis (Fin 3) ℝ Plane),
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p) (C p).source) ∧
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C p).symm (C p).target) ∧
      (∀ p, convexHull ℝ (range (b p)) ⊆ (C p).source) ∧
      (∀ p q, p ≠ q → CoordinateTriangleBoundaryIntersection (C p) (C q) (b p) (b q)) ∧
      (⋃ p, C p '' convexHull ℝ (range (b p))) = closure U := by
  classical
  obtain ⟨H, r, F, positive, d, hr, hrbound, _, _, _, _, haxis, haxis', hsmall, hF,
    hCcompact, hCsub, hCtrace, n, c, L, G, f, ell, _, hc, hfirst, hlast, _,
    B, hB, hsep, hadj, hcapB, hcover⟩ :=
    m64Intrinsic_exists_covered_return_bands hg hT hend hinj hregular hind
      hU hV hdisj hfU hfV hray
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let caps (i : Bool × Bool) :=
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  let A := ⋃ i, ⋃ (_ : occupied i), caps i
  let R := A ∪ ⋃ i, (B i).carrier
  have hrT : r < T := by linarith
  have hcut (j : Fin (n + 1)) : c j ∈ Icc r (T - r) :=
    ⟨by simpa only [hfirst] using hc.monotone (Fin.zero_le j),
      by simpa only [hlast] using hc.monotone (Fin.le_last j)⟩
  have hlower (i : Fin n) : (B i).lowerArc ⊆ gamma '' Icc 0 T := by
    rw [(hB i).1]
    exact image_mono (Icc_subset_Icc (hr.le.trans (hcut i.castSucc).1)
      ((hcut i.succ).2.trans (sub_le_self T hr.le)))
  have hlocal : ∀ p ∈ closure U ∩ gamma '' Icc 0 T, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ R := by
    rintro p ⟨_, t, ht, rfl⟩
    exact hcover t ht
  choose face hface hzero hone htwo Q b hQ hQi hsource hcarrier hboundary using
    fun i : Bool × Bool => m64Intrinsic_exists_coordinate_face_of_chosen_cap (F i)
      hr (hF i).1 (hF i).2.2.1 (hF i).2.2.2.1
  have hfaceunion : (⋃ i, ⋃ (_ : occupied i), (face i).carrier) = A := by
    simp only [hface]
    rfl
  have hsector (i : Bool × Bool) : (face i).carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
    rw [hface]
    exact (hF i).2.2.2.2.2.2.2.1
  have hsecond (i : Bool × Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ((face i).boundary 1).map t = H (sectorParameterEquiv 0 i (0, t * r)) := by
    rw [hone]
    exact (hF i).2.2.2.2.2.1 _ ⟨mul_nonneg ht.1 hr.le,
      mul_le_of_le_one_left hr.le ht.2⟩
  have hfirstedge (i : Bool × Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ((face i).boundary 2).map t = H (sectorParameterEquiv 0 i (t * r, 0)) := by
    rw [htwo]
    exact (hF i).2.2.2.2.1 _ ⟨mul_nonneg ht.1 hr.le,
      mul_le_of_le_one_left hr.le ht.2⟩
  have hchord (i : Bool × Bool) (t : ℝ) : ((face i).boundary 0).map t =
      (1 - t) • H (sectorParameterEquiv 0 i (r, 0)) +
        t • H (sectorParameterEquiv 0 i (0, r)) := by
    rw [hzero, (hF i).2.2.2.2.2.2.1,
      (hF i).2.2.2.2.1 r ⟨hr.le, le_rfl⟩,
      (hF i).2.2.2.2.2.1 r ⟨hr.le, le_rfl⟩]
  have hcoordinates (i : Bool × Bool) :
      ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
        (basis : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
        convexHull ℝ (range basis) ⊆ C.source ∧
        (face i).carrier = C '' convexHull ℝ (range basis) ∧
        ∀ k, ((face i).boundary k).map = C ∘
          affineChartSegment (basis (k.succAbove 0)) (basis (k.succAbove 1)) :=
    ⟨Q i, b i, hQ i, hQi i, hsource i, hcarrier i, hboundary i⟩
  have hCC := m64Intrinsic_retained_caps_canonical_compatibility H hr face Q b hcarrier
    hboundary hsector (fun i => by rw [hface]; exact (hF i).2.2.2.2.2.2.2.2)
    hsmall hsecond hfirstedge
  have hfrontlines := m64Intrinsic_retained_caps_frontier_lines hr hrT.le
    H F positive haxis haxis' (fun i => (hF i).1) (fun i => (hF i).2.2.1)
      (fun i => (hF i).2.2.2.1) (fun i => (hF i).2.2.2.2.1)
      (fun i => (hF i).2.2.2.2.2.1) (fun i => (hF i).2.2.2.2.2.2.1)
      (fun i => (hF i).2.2.2.2.2.2.2.1)
  obtain ⟨_, _, caplines, hcaplines, hcapfront⟩ := hfrontlines
  let pieces : Option (Fin n) → Set AnnulusCoordinates
    | none => A
    | some i => (B i).carrier
  have hpieces : (⋃ i, pieces i) = R := by
    ext z
    simp only [pieces, R, mem_iUnion, Option.exists, mem_union]
  have hclosed (i : Option (Fin n)) : IsClosed (pieces i) := by
    cases i with
    | none => exact hCcompact.isClosed
    | some i => exact (isCompact_iUnion (fun j => ((B i).face j).isCompact_carrier)).isClosed
  have hsub (i : Option (Fin n)) : pieces i ⊆ closure U := by
    cases i with
    | none => exact hCsub
    | some i => exact (hB i).2.2.2.1
  have hlinefamily (i : Option (Fin n)) :
      ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
        (∀ l ∈ lines, Function.Surjective l) ∧
        frontier (pieces i) \ gamma '' Icc 0 T ⊆ ⋃ l ∈ lines, {z | l z = 0} := by
    cases i with
    | none => exact ⟨caplines, hcaplines, fun z hz => (hcapfront hz.1).resolve_left hz.2⟩
    | some i =>
      obtain ⟨lines, hlines, hfront⟩ := m64Intrinsic_linear_band_frontier_lines (L i).symm (B i)
      exact ⟨lines, hlines, fun z hz => (hfront hz.1).resolve_left
        (fun h => hz.2 (hlower i h))⟩
  obtain ⟨lines, hlines, hlinesub⟩ := Poincare.Topology.Plane.exists_affine_lines_iUnion
    (fun i => frontier (pieces i) \ gamma '' Icc 0 T) hlinefamily
  have hfront (i : Option (Fin n)) : frontier (pieces i) ⊆ gamma '' Icc 0 T ∪
      (chartAt AnnulusCoordinates (0 : AnnulusCoordinates)) ⁻¹'
        (⋃ l ∈ lines, {z | l z = 0}) := by
    intro z hz
    by_cases htrace : z ∈ gamma '' Icc 0 T
    · exact Or.inl htrace
    · right
      simpa using hlinesub (mem_iUnion.mpr ⟨i, hz, htrace⟩)
  obtain ⟨core, hcore, _, _, _, hrecovery, _, _⟩ :=
    exists_exact_polygonal_remainder_mesh_with_refinement (0 : AnnulusCoordinates)
      hU hcompact (by intro z _; simp) pieces hclosed hsub (subset_of_eq hfU)
      lines hlines hfront (by simpa only [hpieces] using hlocal)
  have hcore' : core.toPlaneComplex.support = closure (U \ R) := by
    simpa only [hpieces, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, image_id] using hcore
  have hrecovery' : closure U = R ∪ core.toPlaneComplex.support := by
    simpa [hpieces] using hrecovery
  have haxes : (fun t : ℝ => H (0, t * r)) '' Icc 0 1 ∪
      (fun t : ℝ => H (t * r, 0)) '' Icc 0 1 ⊆ gamma '' Icc 0 T := by
    rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · dsimp only
      rw [haxis']
      refine ⟨T - t * r, ?_, rfl⟩
      constructor <;> nlinarith [ht.1, ht.2]
    · dsimp only
      rw [haxis]
      exact ⟨t * r, ⟨mul_nonneg ht.1 hr.le,
        (mul_le_of_le_one_left hr.le ht.2).trans hrT.le⟩, rfl⟩
  obtain ⟨mesh, hmesh, _, hmeshcap, hmeshband⟩ :=
    m64Intrinsic_refine_core_to_retained_caps_and_bands H r face positive Q b hQ hQi
      hsource hcarrier hboundary hsector hsecond hfirstedge hchord
      (fun i => collarParameterEquiv.trans (L i).symm) f _ _ _ _ _ _ _ _ B
      haxes (by rw [hfaceunion]; exact subset_union_left)
      (fun i => fun _ hz => Or.inr (mem_iUnion.mpr ⟨i, hz⟩)) hlower hlocal core hcore'
  let cut (j : Fin (n + 1)) := segment ℝ (gamma (c j)) (gamma (c j) + ell • d (c j))
  have hBB := m64Intrinsic_band_chain_faces_canonical _ _ _ _ _ _ _ _ _ _ B cut
    (fun i => (hB i).2.1) (fun i => (hB i).2.2.1) hsep hadj
  have hcuts (i : Fin n) (right : Bool) : ∃ u v : AnnulusCoordinates,
      ((B i).endpointEdge right).map '' Icc (0 : ℝ) 1 = segment ℝ u v := by
    rw [(B i).endpointEdge_image]
    cases right
    · exact ⟨_, _, (hB i).2.1⟩
    · exact ⟨_, _, (hB i).2.2.1⟩
  have houter (i : Fin n) : A ∩ (B i).carrier ⊆ (B i).leftCut ∪ (B i).rightCut := by
    rw [hcapB i]
    split_ifs <;> simp
  have htraceDisjoint : Disjoint U (gamma '' Icc 0 T) := by
    rw [← hfU]
    exact (disjoint_frontier_iff_isOpen.mpr hU).symm
  have hownchord (i : Fin n) (j : Bool × Bool) (hj : occupied j) :
      (face j).carrier ∩ (B i).carrier ⊆ ((face j).boundary 0).map '' Icc (0 : ℝ) 1 := by
    apply m64Intrinsic_retained_cap_band_inter_subset_chord H hr hrT face positive
      (by simpa [sectorParameterEquiv_apply] using hsmall (true, true) r ⟨hr.le, le_rfl⟩)
      hsector hsecond hfirstedge hchord hcoordinates hend hinj haxis haxis' (B i)
      htraceDisjoint ?_ (hB i).2.2.2.2 ?_ ?_ j hj
    · rw [(hB i).1]
      exact image_mono (Icc_subset_Icc (hcut i.castSucc).1 (hcut i.succ).2)
    · simpa only [hface] using hCtrace.subset
    · simpa only [hface] using houter i
  let J := {j : Bool × Bool // occupied j}
  have hchordimage (j : J) : Q j '' affineSegment ℝ (b j ((0 : Fin 3).succAbove 0))
      (b j ((0 : Fin 3).succAbove 1)) = segment ℝ
        (H (sectorParameterEquiv 0 j (r, 0))) (H (sectorParameterEquiv 0 j (0, r))) := by
    rw [← Euler.affineChartSegment_image, ← image_comp, ← hboundary]
    rw [segment_eq_image]
    apply image_congr
    intro t _
    exact hchord j t
  obtain ⟨m, C, bases, hC, hCi, hCs, hCp, hCsupport⟩ :=
    m64Intrinsic_exists_cap_band_core_coordinate_parents _ _ _ _ _ _ _ _ _ _ B
      (fun i => contMDiffOn_iff_contDiffOn.mpr
        (collarParameterEquiv.trans (L i).symm).contDiff.contDiffOn)
      (fun i => contMDiffOn_iff_contDiffOn.mpr
        (collarParameterEquiv.trans (L i).symm).symm.contDiff.contDiffOn)
      hBB hcuts (fun j : J => Q j) (fun j => b j) (fun j => hQ j)
      (fun j => hQi j) (fun j => hsource j)
      (fun j k h => hCC j k (fun he => h (Subtype.ext he)))
      (fun _ => 0) (fun j => H (sectorParameterEquiv 0 j (r, 0)))
      (fun j => H (sectorParameterEquiv 0 j (0, r))) hchordimage
      (by
        intro i j z hz
        apply houter i
        rw [← hcarrier] at hz
        have hzcap : z ∈ caps j := by simpa only [caps, ← hface] using hz.2
        exact ⟨mem_iUnion.mpr ⟨j.1, mem_iUnion.mpr ⟨j.2, hzcap⟩⟩, hz.1⟩)
      (by
        intro i j z hz
        rw [← Euler.affineChartSegment_image, ← image_comp, ← hboundary]
        apply hownchord i j j.2
        exact ⟨(hcarrier j).symm ▸ hz.2, hz.1⟩)
      mesh (fun t j => hmeshcap j j.2 t) (fun t i p => hmeshband i t p)
  refine ⟨m, C, bases, hC, hCi, hCs, hCp, ?_⟩
  have hchosen : (⋃ j : J, Q j '' convexHull ℝ (range (b j))) = A := by
    ext z
    simp only [J, A, caps, mem_iUnion, Subtype.exists, ← hcarrier, hface]
  rw [hCsupport, hchosen, hmesh]
  exact hrecovery'.symm

end PoincareConjecture
