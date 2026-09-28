import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerSeams
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReflexCornerCaps
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FittedCornerFrontier













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_reflex_corner_frontier_subset
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : ℝ)
    (F : Bool × Bool → SmoothFace AnnulusCoordinates)
    (hsub : ∀ i, (F i).carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (hsecond : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((F i).boundary 1).map t =
      H (sectorParameterEquiv 0 i (0, t * r)))
    (hfirst : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((F i).boundary 2).map t =
      H (sectorParameterEquiv 0 i (t * r, 0)))
    (hchord : ∀ i t, ((F i).boundary 0).map t =
      (1 - t) • H (sectorParameterEquiv 0 i (r, 0)) +
        t • H (sectorParameterEquiv 0 i (0, r)))
    (hcoordinates : ∀ i, ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
      (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
      convexHull ℝ (range b) ⊆ C.source ∧
      (F i).carrier = C '' convexHull ℝ (range b) ∧
      ∀ k, ((F i).boundary k).map = C ∘
        affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) :
    let idx : Fin 3 → Bool × Bool := ![(false, false), (false, true), (true, false)]
    frontier (⋃ i, (F (idx i)).carrier) ⊆
      (fun t : ℝ => H (0, t * r)) '' Icc 0 1 ∪
        (fun t : ℝ => H (t * r, 0)) '' Icc 0 1 ∪
        ⋃ i, ((F (idx i)).boundary 0).map '' Icc (0 : ℝ) 1 := by
  classical
  dsimp only
  let idx : Fin 3 → Bool × Bool := ![(false, false), (false, true), (true, false)]
  let f (i : Fin 3) := F (idx i)
  let S := ⋃ i, (f i).carrier
  let E := (fun t : ℝ => H (0, t * r)) '' Icc 0 1 ∪
    (fun t : ℝ => H (t * r, 0)) '' Icc 0 1 ∪
      ⋃ i, ((f i).boundary 0).map '' Icc (0 : ℝ) 1
  have hclosed : IsClosed S := isClosed_iUnion_of_finite (fun i => (f i).isClosed_carrier)
  have hinto (i : Fin 3) : (f i).carrier ⊆ S := by
    intro z hz
    exact mem_iUnion.mpr ⟨i, hz⟩
  have hpairSub (i j : Fin 3) : (f i).carrier ∪ (f j).carrier ⊆ S :=
    union_subset (hinto i) (hinto j)
  have hfirstEq (i j : Bool × Bool) (hij : i.1 = j.1) :
      EqOn ((F i).boundary 2).map ((F j).boundary 2).map (Icc (0 : ℝ) 1) := by
    intro t ht
    rw [hfirst i t ht, hfirst j t ht]
    simp only [sectorParameterEquiv_apply, hij, neg_zero, ite_self]
  have hsecondEq (i j : Bool × Bool) (hij : i.2 = j.2) :
      EqOn ((F i).boundary 1).map ((F j).boundary 1).map (Icc (0 : ℝ) 1) := by
    intro t ht
    rw [hsecond i t ht, hsecond j t ht]
    simp only [sectorParameterEquiv_apply, hij, neg_zero, ite_self]
  have hshared (i j : Fin 3) (hij : idx i ≠ idx j) (k : Fin 3)
      (heq : EqOn ((f i).boundary k).map ((f j).boundary k).map (Icc (0 : ℝ) 1))
      {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      ((f i).boundary k).map t ∈ interior S := by
    obtain ⟨C, b, _, _, hb, hfc, hfb⟩ := hcoordinates (idx i)
    obtain ⟨D, c, _, _, hc, hgc, hgb⟩ := hcoordinates (idx j)
    apply interior_mono (hpairSub i j)
    exact m64Intrinsic_corner_shared_edge_mem_interior H (f i) (f j) C D b c
      hb hc hfc hgc hfb hgb hij (hsub (idx i)) (hsub (idx j)) k k heq ht
  have hzeroE : H 0 ∈ E := by
    apply Or.inl
    refine Or.inl ⟨0, by simp, ?_⟩
    change H (0, 0 * r) = H 0
    rw [zero_mul]
    rfl
  have hchordE (i : Fin 3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      ((f i).boundary 0).map t ∈ E :=
    Or.inr (mem_iUnion.mpr ⟨i, t, ht, rfl⟩)
  have hinternal (i : Fin 3) (k : Fin 3) (hk : k = 1 ∨ k = 2)
      (hi : ∀ t ∈ Ioo (0 : ℝ) 1, ((f i).boundary k).map t ∈ interior S)
      {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
      (hf : ((f i).boundary k).map t ∈ frontier S) :
      ((f i).boundary k).map t ∈ E := by
    by_cases hzero : t = 0
    · subst t
      rcases hk with rfl | rfl
      · change ((F (idx i)).boundary 1).map 0 ∈ E
        rw [hsecond (idx i) 0 (by simp), zero_mul]
        change H (sectorParameterEquiv 0 (idx i) 0) ∈ E
        rwa [sectorParameterEquiv_zero]
      · change ((F (idx i)).boundary 2).map 0 ∈ E
        rw [hfirst (idx i) 0 (by simp), zero_mul]
        change H (sectorParameterEquiv 0 (idx i) 0) ∈ E
        rwa [sectorParameterEquiv_zero]
    by_cases hone : t = 1
    · subst t
      rcases hk with rfl | rfl
      · have heq : ((f i).boundary 1).map 1 = ((f i).boundary 0).map 1 := by
          simp [f, hsecond (idx i) 1 (by simp), hchord]
        exact heq ▸ hchordE i (by simp)
      · have heq : ((f i).boundary 2).map 1 = ((f i).boundary 0).map 0 := by
          simp [f, hfirst (idx i) 1 (by simp), hchord]
        exact heq ▸ hchordE i (by simp)
    exact False.elim (hf.2 (hi t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩))
  change frontier S ⊆ E
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hclosed.frontier_subset hz)
  have hfi : z ∈ frontier (f i).carrier :=
    ⟨subset_closure hi, fun h => hz.2 (interior_mono (hinto i) h)⟩
  rw [(f i).boundary_carrier] at hfi
  obtain ⟨k, t, ht, rfl⟩ := mem_iUnion.mp hfi
  fin_cases i <;> fin_cases k
  · exact hchordE 0 ht
  · exact hinternal 0 1 (Or.inl rfl)
      (fun _ ht' => hshared 0 2 (by decide) 1
        (hsecondEq (false, false) (true, false) rfl) ht') ht hz
  · exact hinternal 0 2 (Or.inr rfl)
      (fun _ ht' => hshared 0 1 (by decide) 2
        (hfirstEq (false, false) (false, true) rfl) ht') ht hz
  · exact hchordE 1 ht
  · apply Or.inl
    apply Or.inl
    refine ⟨t, ht, ?_⟩
    simpa [f, idx, sectorParameterEquiv_apply] using (hsecond (false, true) t ht).symm
  · exact hinternal 1 2 (Or.inr rfl)
      (fun _ ht' => hshared 1 0 (by decide) 2
        (hfirstEq (false, true) (false, false) rfl) ht') ht hz
  · exact hchordE 2 ht
  · exact hinternal 2 1 (Or.inl rfl)
      (fun _ ht' => hshared 2 0 (by decide) 1
        (hsecondEq (true, false) (false, false) rfl) ht') ht hz
  · apply Or.inl
    apply Or.inr
    refine ⟨t, ht, ?_⟩
    simpa [f, idx, sectorParameterEquiv_apply] using (hfirst (true, false) t ht).symm





theorem m64Intrinsic_exists_reflex_loop_corner_patch
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target)
    {K : Set AnnulusCoordinates}
    (hside : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), H z ∈ K ↔ z.1 ≤ 0 ∨ z.2 ≤ 0)
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} (hT : 0 < T)
    (haxis : ∀ s, H (s, 0) = gamma s)
    (haxis' : ∀ s, H (0, s) = gamma (T - s)) :
    ∃ (face : Fin 3 → SmoothFace AnnulusCoordinates)
      (lines : Fin 3 → AnnulusCoordinates →ᵃ[ℝ] ℝ) (W : Set AnnulusCoordinates),
      IsCompact (⋃ i, (face i).carrier) ∧ (∀ i, (face i).carrier ⊆ K) ∧
      (∀ i j, i ≠ j → Disjoint (interior (face i).carrier) (interior (face j).carrier)) ∧
      frontier (⋃ i, (face i).carrier) ⊆
        gamma '' Icc 0 T ∪ ⋃ i, {z | lines i z = 0} ∧
      (∀ i, Function.Surjective (lines i)) ∧
      IsOpen W ∧ H 0 ∈ W ∧ W ∩ K ⊆ ⋃ i, (face i).carrier ∧
      (∀ i, ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
        (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
        convexHull ℝ (range b) ⊆ C.source ∧
        (face i).carrier = C '' convexHull ℝ (range b) ∧
        ∀ k, ((face i).boundary k).map = C ∘
          affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) := by
  classical
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hside
  let J := H.restrOpen (ball (0 : ℝ × ℝ) R) isOpen_ball
  have hJ0 : (0 : ℝ × ℝ) ∈ J.source := ⟨h0, mem_ball_self hR⟩
  have hJ : ContDiffOn ℝ ∞ J J.source := hH.mono (fun _ hz => hz.1)
  have hJi : ContDiffOn ℝ ∞ J.symm J.target := hHi.mono (fun _ hz => hz.1)
  obtain ⟨r, F, W, hr, hrT, hW, hpW, hWt, hsub, hcover, hsecond, hfirst,
      hchord, _, _, _, hcoordinates⟩ :=
    m64Intrinsic_exists_four_corner_faces J hJ0 hJ hJi hT
  let idx : Fin 3 → Bool × Bool := ![(false, false), (false, true), (true, false)]
  let face (i : Fin 3) := F (idx i)
  have hidx : Function.Injective idx := by
    intro i j heq
    fin_cases i <;> fin_cases j <;> simp [idx] at heq ⊢
  have hsectorK (i : Fin 3) : (face i).carrier ⊆ K := by
    intro z hz
    obtain ⟨q, ⟨hq, ⟨p, hp, rfl⟩⟩, rfl⟩ := hsub (idx i) hz
    apply (hball hq.2).mpr
    fin_cases i <;> simp [idx, sectorParameterEquiv_apply, hp.1, hp.2]
  have hcoverK : W ∩ K ⊆ ⋃ i, (face i).carrier := by
    intro z hz
    have hzt : z ∈ J.target := hWt hz.1
    let q := J.symm z
    have hq : q ∈ J.source := J.map_target hzt
    have hqz : J q = z := J.right_inv hzt
    have hqside : q.1 ≤ 0 ∨ q.2 ≤ 0 := by
      apply (hball hq.2).mp
      change J q ∈ K
      rw [hqz]
      exact hz.2
    have hmember (i : Fin 3) (p : ℝ × ℝ) (hp : 0 ≤ p.1 ∧ 0 ≤ p.2)
        (he : sectorParameterEquiv 0 (idx i) p = q) : z ∈ (face i).carrier := by
      apply hcover (idx i)
      exact ⟨hz.1, q, ⟨hq, p, hp, he⟩, hqz⟩
    by_cases hq1 : q.1 ≤ 0
    · by_cases hq2 : q.2 ≤ 0
      · exact mem_iUnion.mpr ⟨0, hmember 0 (-q.1, -q.2)
          ⟨neg_nonneg.mpr hq1, neg_nonneg.mpr hq2⟩ (by
            simp [idx, sectorParameterEquiv_apply])⟩
      · exact mem_iUnion.mpr ⟨1, hmember 1 (-q.1, q.2)
          ⟨neg_nonneg.mpr hq1, (lt_of_not_ge hq2).le⟩ (by
            simp [idx, sectorParameterEquiv_apply])⟩
    · exact mem_iUnion.mpr ⟨2, hmember 2 (q.1, -q.2)
        ⟨(lt_of_not_ge hq1).le, neg_nonneg.mpr (hqside.resolve_left hq1)⟩ (by
          simp [idx, sectorParameterEquiv_apply])⟩
  choose lines hlines hline using fun i : Fin 3 =>
    Poincare.Topology.Plane.exists_affine_line_containing_segment
      (J (sectorParameterEquiv 0 (idx i) (r, 0)))
      (J (sectorParameterEquiv 0 (idx i) (0, r)))
  have hchordLine (i : Fin 3) : ((face i).boundary 0).map '' Icc (0 : ℝ) 1 ⊆
      {z | lines i z = 0} := by
    rintro z ⟨t, ht, rfl⟩
    rw [hchord]
    apply hline i
    rw [segment_eq_image_lineMap]
    refine ⟨t, ht, ?_⟩
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hfront := m64Intrinsic_reflex_corner_frontier_subset J r F
    hsub hsecond hfirst hchord hcoordinates
  refine ⟨face, lines, W, isCompact_iUnion (fun i => (face i).isCompact_carrier_image),
    hsectorK, ?_, ?_, hlines, hW, hpW, hcoverK, fun i => hcoordinates (idx i)⟩
  · intro i j hij
    apply (face i).disjoint_interiors_of_inter_subset_frontier (face j)
    exact m64Intrinsic_corner_carriers_inter_subset_frontier J (face i).isClosed_carrier
      (fun h => hij (hidx h)) (hsub (idx i)) (hsub (idx j))
  · intro z hz
    rcases hfront hz with (hv | hh) | hc
    · left
      obtain ⟨t, ht, rfl⟩ := hv
      change H (0, t * r) ∈ gamma '' Icc 0 T
      rw [haxis']
      refine ⟨T - t * r, ?_, rfl⟩
      constructor <;> nlinarith [ht.1, ht.2, hr, hrT]
    · left
      obtain ⟨t, ht, rfl⟩ := hh
      change H (t * r, 0) ∈ gamma '' Icc 0 T
      rw [haxis]
      refine ⟨t * r, ?_, rfl⟩
      constructor <;> nlinarith [ht.1, ht.2, hr, hrT]
    · right
      obtain ⟨i, hi⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨i, hchordLine i hi⟩

end PoincareConjecture
