import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ExposedCapChords
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapAttachmentCuts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ObstacleBarriers

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_cap_positive_tip_on_chord
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ} (hr : 0 < r)
    (face : SmoothFace AnnulusCoordinates) (i : Bool × Bool)
    (hsub : face.carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (hchord : ∀ t, (face.boundary 0).map t =
      (1 - t) • H (sectorParameterEquiv 0 i (r, 0)) +
        t • H (sectorParameterEquiv 0 i (0, r)))
    (hsource : (r, 0) ∈ H.source ∧ (0, r) ∈ H.source) :
    ({H (r, 0), H (0, r)} : Set AnnulusCoordinates) ∩ face.carrier ⊆
      (face.boundary 0).map '' Icc (0 : ℝ) 1 := by
  rintro x ⟨hx, hxface⟩
  obtain ⟨z, ⟨hzsource, q, hq, hqz⟩, hzx⟩ := hsub hxface
  rcases hx with hx | hx
  · have hz : z = (r, 0) := H.injOn hzsource hsource.1 (hzx.trans hx)
    have hi : i.1 = true := by
      have h := congrArg Prod.fst (hqz.trans hz)
      rcases i with ⟨i, j⟩
      cases i
      · simp only [sectorParameterEquiv_apply, Bool.false_eq_true, ↓reduceIte] at h
        dsimp at h
        linarith [hq.1]
      · rfl
    refine ⟨0, by simp, ?_⟩
    rw [hchord]
    simpa [hi, sectorParameterEquiv_apply] using hx.symm
  · have hx' := mem_singleton_iff.mp hx
    have hz : z = (0, r) := H.injOn hzsource hsource.2 (hzx.trans hx')
    have hi : i.2 = true := by
      have h := congrArg Prod.snd (hqz.trans hz)
      rcases i with ⟨i, j⟩
      cases j
      · simp only [sectorParameterEquiv_apply, Bool.false_eq_true, ↓reduceIte] at h
        dsimp at h
        linarith [hq.2]
      · rfl
    refine ⟨1, by simp, ?_⟩
    rw [hchord]
    simpa [hi, sectorParameterEquiv_apply] using hx'.symm

theorem m64Intrinsic_retained_cap_band_inter_subset_chord
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r T : ℝ}
    (hr : 0 < r) (hrT : r < T)
    (face : Bool × Bool → SmoothFace AnnulusCoordinates) (positive : Bool)
    (hsource : (r, 0) ∈ H.source ∧ (0, r) ∈ H.source)
    (hsub : ∀ i, (face i).carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (hsecond : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((face i).boundary 1).map t =
      H (sectorParameterEquiv 0 i (0, t * r)))
    (hfirst : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((face i).boundary 2).map t =
      H (sectorParameterEquiv 0 i (t * r, 0)))
    (hchord : ∀ i t, ((face i).boundary 0).map t =
      (1 - t) • H (sectorParameterEquiv 0 i (r, 0)) +
        t • H (sectorParameterEquiv 0 i (0, r)))
    (hcoordinates : ∀ i, ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
      (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
      convexHull ℝ (range b) ⊆ C.source ∧
      (face i).carrier = C '' convexHull ℝ (range b) ∧
      ∀ k, ((face i).boundary k).map = C ∘
        affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)))
    {gamma : ℝ → AnnulusCoordinates}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (haxis : ∀ s : ℝ, H (s, 0) = gamma s)
    (haxis' : ∀ s : ℝ, H (0, s) = gamma (T - s))
    {G : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces G lo a b ua wa ub wb ra rb)
    {U : Set AnnulusCoordinates} (hdisj : Disjoint U (gamma '' Icc 0 T))
    (hlower : B.lowerArc ⊆ gamma '' Icc r (T - r))
    (hregion : B.carrier \ B.lowerArc ⊆ U) :
    let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
    let A := ⋃ i, ⋃ (_ : occupied i), (face i).carrier
    A ∩ gamma '' Icc 0 T ⊆ gamma '' Icc 0 r ∪ gamma '' Icc (T - r) T →
    A ∩ B.carrier ⊆ B.leftCut ∪ B.rightCut →
    ∀ i, occupied i → (face i).carrier ∩ B.carrier ⊆
      ((face i).boundary 0).map '' Icc (0 : ℝ) 1 := by
  classical
  dsimp only
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let A := ⋃ i, ⋃ (_ : occupied i), (face i).carrier
  intro hcontact hinter i hi x hx
  have hfaceA : (face i).carrier ⊆ A := fun z hz =>
    mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hz⟩⟩
  have hxA := hfaceA hx.1
  have hxfront : x ∈ frontier A :=
    m64Intrinsic_band_cap_inter_subset_frontier B (Subset.refl A) hinter ⟨hxA, hx.2⟩
  have hexposed := m64Intrinsic_retained_cap_exposed_chord H r face positive
    hsub hsecond hfirst hchord hcoordinates i hi ⟨hxfront, hx.1⟩
  rcases hexposed with haxisx | hchordx
  · have hxtrace : x ∈ gamma '' Icc (0 : ℝ) T := by
      rcases haxisx with ⟨s, hs, hsx⟩ | ⟨s, hs, hsx⟩
      · refine ⟨T - s * r, ?_, ?_⟩
        · constructor <;> nlinarith [mul_nonneg hs.1 hr.le,
            mul_le_of_le_one_left hr.le hs.2]
        · simpa only [haxis'] using hsx
      · refine ⟨s * r, ?_, ?_⟩
        · exact ⟨mul_nonneg hs.1 hr.le, (mul_le_of_le_one_left hr.le hs.2).trans hrT.le⟩
        · simpa only [haxis] using hsx
    have hxlower : x ∈ B.lowerArc := by
      by_contra hn
      exact disjoint_left.mp hdisj (hregion ⟨hx.2, hn⟩) hxtrace
    obtain ⟨t, ht, htx⟩ := hlower hxlower
    have htends : t = r ∨ t = T - r := by
      by_cases htr : t = r
      · exact Or.inl htr
      by_cases htT : t = T - r
      · exact Or.inr htT
      exact False.elim (m64Intrinsic_trimmed_arc_avoids_caps hr hrT hend hinj hcontact t
        ⟨lt_of_le_of_ne ht.1 (Ne.symm htr), lt_of_le_of_ne ht.2 htT⟩ (htx.symm ▸ hxA))
    apply m64Intrinsic_cap_positive_tip_on_chord H hr (face i) i (hsub i) (hchord i) hsource
    refine ⟨?_, hx.1⟩
    rcases htends with rfl | rfl
    · left
      rw [haxis]
      exact htx.symm
    · right
      rw [mem_singleton_iff, haxis']
      exact htx.symm
  · exact hchordx

end PoincareConjecture
