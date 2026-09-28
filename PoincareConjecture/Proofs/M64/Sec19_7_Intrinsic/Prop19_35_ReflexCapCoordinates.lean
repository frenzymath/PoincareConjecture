import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CommonCapCoordinates
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapChordSigns

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Matrix
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_reflex_cap_coordinates_with_chords
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • quarterTurn (deriv gamma t) ∈ U)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source) (hbase : H 0 = gamma 0)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target)
    (haxis : ∀ s : ℝ, H (s, 0) = gamma s)
    (haxis' : ∀ s : ℝ, H (0, s) = gamma (T - s))
    (hside : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), H z ∈ closure U ↔ z.1 ≤ 0 ∨ z.2 ≤ 0) :
    ∃ (r : ℝ) (F : Fin 3 → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (W : Set AnnulusCoordinates),
      0 < r ∧ r ≤ T / 3 ∧ IsOpen W ∧ gamma 0 ∈ W ∧
      (∀ i, {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source ∧
        ContDiffOn ℝ ∞ (F i) (F i).source ∧
        ContDiffOn ℝ ∞ (F i).symm (F i).target ∧
        (∀ s ∈ Icc (0 : ℝ) r, F i (s, 0) =
          H (sectorParameterEquiv 0 (![ (false, false), (false, true), (true, false)] i) (s, 0))) ∧
        (∀ s ∈ Icc (0 : ℝ) r, F i (0, s) =
          H (sectorParameterEquiv 0 (![ (false, false), (false, true), (true, false)] i) (0, s))) ∧
        (∀ t : ℝ, F i ((1 - t) * r, t * r) =
          (1 - t) • F i (r, 0) + t • F i (0, r)) ∧
        F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ closure U) ∧
      W ∩ closure U ⊆ ⋃ i, F i ''
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ∧
      0 < inner ℝ (quarterTurn (deriv gamma r)) (F 2 (0, r) - F 2 (r, 0)) ∧
      0 < inner ℝ (quarterTurn (deriv gamma (T - r))) (F 1 (r, 0) - F 1 (0, r)) := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hside
  let J := H.restrOpen (ball (0 : ℝ × ℝ) R) isOpen_ball
  have hJ0 : (0 : ℝ × ℝ) ∈ J.source := ⟨h0, mem_ball_self hR⟩
  have hJ : ContDiffOn ℝ ∞ J J.source := hH.mono inter_subset_left
  have hJi : ContDiffOn ℝ ∞ J.symm J.target := hHi.mono inter_subset_left
  obtain ⟨r, A, W, hr, hrT, hW, hpW, hWt, hA⟩ :=
    m64Intrinsic_exists_four_corner_cap_coordinates J hJ0 hJ hJi
      (show (0 : ℝ) < T / 3 by positivity)
  let idx : Fin 3 → Bool × Bool := ![(false, false), (false, true), (true, false)]
  let F (i : Fin 3) := A (idx i)
  have hsub (i : Fin 3) : F i ''
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ closure U := by
    intro z hz
    obtain ⟨q, ⟨hq, p, hp, rfl⟩, rfl⟩ := (hA (idx i)).2.2.2.2.2.2.1 hz
    apply (hball hq.2).mpr
    fin_cases i <;> simp [idx, sectorParameterEquiv_apply, hp.1, hp.2]
  have hcover : W ∩ closure U ⊆ ⋃ i, F i ''
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
    intro z hz
    have hzt : z ∈ J.target := hWt hz.1
    let q := J.symm z
    have hq : q ∈ J.source := J.map_target hzt
    have hqz : J q = z := J.right_inv hzt
    have hqside : q.1 ≤ 0 ∨ q.2 ≤ 0 := by
      apply (hball hq.2).mp
      change J q ∈ closure U
      rw [hqz]
      exact hz.2
    have hmember (i : Fin 3) (p : ℝ × ℝ) (hp : 0 ≤ p.1 ∧ 0 ≤ p.2)
        (he : sectorParameterEquiv 0 (idx i) p = q) : z ∈ F i ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} :=
      (hA (idx i)).2.2.2.2.2.2.2 ⟨hz.1, q, ⟨hq, p, hp, he⟩, hqz⟩
    by_cases hq1 : q.1 ≤ 0
    · by_cases hq2 : q.2 ≤ 0
      · exact mem_iUnion.mpr ⟨0, hmember 0 (-q.1, -q.2)
          ⟨neg_nonneg.mpr hq1, neg_nonneg.mpr hq2⟩ (by simp [idx, sectorParameterEquiv_apply])⟩
      · exact mem_iUnion.mpr ⟨1, hmember 1 (-q.1, q.2)
          ⟨neg_nonneg.mpr hq1, (lt_of_not_ge hq2).le⟩ (by simp [idx, sectorParameterEquiv_apply])⟩
    · have hq2 := hqside.resolve_left hq1
      exact mem_iUnion.mpr ⟨2, hmember 2 (q.1, -q.2)
        ⟨(lt_of_not_ge hq1).le, neg_nonneg.mpr hq2⟩ (by simp [idx, sectorParameterEquiv_apply])⟩
  have hsmall : r < T := hrT.trans_lt (by linarith)
  have hleftAxis : ∀ s ∈ Icc (0 : ℝ) r, F 2 (s, 0) = gamma s := by
    intro s hs
    simpa [F, idx, sectorParameterEquiv_apply, J, haxis] using
        (hA (idx 2)).2.2.2.1 s hs
  have hrightAxis : ∀ s ∈ Icc (0 : ℝ) r, F 1 (0, s) = gamma (T - s) := by
    intro s hs
    simpa [F, idx, sectorParameterEquiv_apply, J, haxis'] using
        (hA (idx 1)).2.2.2.2.1 s hs
  have hleftSign := m64Intrinsic_cap_endpoint_chord_sign hg hend hinj hregular
    hU hV hdisj hfU hfV hray hr hsmall (F 2) (hA (idx 2)).1 (hA (idx 2)).2.1
      (hA (idx 2)).2.2.1 (hA (idx 2)).2.2.2.2.2.1 (hsub 2) false false hleftAxis
  have hrightSign := m64Intrinsic_cap_endpoint_chord_sign hg hend hinj hregular
    hU hV hdisj hfU hfV hray hr hsmall (F 1) (hA (idx 1)).1 (hA (idx 1)).2.1
      (hA (idx 1)).2.2.1 (hA (idx 1)).2.2.2.2.2.1 (hsub 1) true true hrightAxis
  refine ⟨r, F, W, hr, hrT, hW, ?_, ?_, hcover, hleftSign, hrightSign⟩
  · simpa [J, hbase] using hpW
  · intro i
    exact ⟨(hA (idx i)).1, (hA (idx i)).2.1, (hA (idx i)).2.2.1,
      (hA (idx i)).2.2.2.1, (hA (idx i)).2.2.2.2.1,
      (hA (idx i)).2.2.2.2.2.1, hsub i⟩

end PoincareConjecture
